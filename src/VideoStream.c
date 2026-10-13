#include "Limelight-internal.h"

#include <stdio.h>

#define FIRST_FRAME_MAX 1500
#define FIRST_FRAME_TIMEOUT_SEC 10

#define FIRST_FRAME_PORT 47996

static RTP_VIDEO_QUEUE rtpQueue;

static SOCKET rtpSocket = INVALID_SOCKET;
static SOCKET firstFrameSocket = INVALID_SOCKET;

static PPLT_CRYPTO_CONTEXT decryptionCtx;

static PLT_THREAD udpPingThread;
static PLT_THREAD receiveThread;
static PLT_THREAD decoderThread;

static bool receivedDataFromPeer;
static uint64_t firstDataTimeMs;
static bool receivedFullFrame;

// We can't request an IDR frame until the depacketizer knows
// that a packet was lost. This timeout bounds the time that
// the RTP queue will wait for missing/reordered packets.
#define RTP_QUEUE_DELAY 10

// This is the desired number of video packets that can be
// stored in the socket's receive buffer. 2048 is chosen
// because it should be large enough for all reasonable
// frame sizes (probably 2 or 3 frames) without using too
// much kernel memory with larger packet sizes. It also
// can smooth over transient pauses in network traffic
// and subsequent packet/frame bursts that follow.
#define RTP_RECV_PACKETS_BUFFERED 2048

// Initialize the video stream
void initializeVideoStream(void) {
    initializeVideoDepacketizer(StreamConfig.packetSize);
    RtpvInitializeQueue(&rtpQueue);
    decryptionCtx = PltCreateCryptoContext();
    receivedDataFromPeer = false;
    firstDataTimeMs = 0;
    receivedFullFrame = false;
}

// Clean up the video stream
void destroyVideoStream(void) {
    PltDestroyCryptoContext(decryptionCtx);
    destroyVideoDepacketizer();
    RtpvCleanupQueue(&rtpQueue);
}

// UDP Ping proc
static void VideoPingThreadProc(void* context) {
    char legacyPingData[] = { 0x50, 0x49, 0x4E, 0x47 };
    LC_SOCKADDR saddr;

    LC_ASSERT(VideoPortNumber != 0);

    memcpy(&saddr, &RemoteAddr, sizeof(saddr));
    SET_PORT(&saddr, VideoPortNumber);

    // We do not check for errors here. Socket errors will be handled
    // on the read-side in ReceiveThreadProc(). This avoids potential
    // issues related to receiving ICMP port unreachable messages due
    // to sending a packet prior to the host PC binding to that port.
    int pingCount = 0;
    while (!PltIsThreadInterrupted(&udpPingThread)) {
        if (VideoPingPayload.payload[0] != 0) {
            pingCount++;
            VideoPingPayload.sequenceNumber = BE32(pingCount);

            sendto(rtpSocket, (char*)&VideoPingPayload, sizeof(VideoPingPayload), 0, (struct sockaddr*)&saddr, AddrLen);
        }
        else {
            sendto(rtpSocket, legacyPingData, sizeof(legacyPingData), 0, (struct sockaddr*)&saddr, AddrLen);
        }

        PltSleepMsInterruptible(&udpPingThread, 500);
    }
}

// Receive thread proc
// FrogtaleTV patch: cross-frame reorder hold for satellite links.
//
// Starlink stalls video for ~30-50 ms at each 15 s satellite handoff and then delivers the
// backlog, partly out of order. RtpVideoQueue only holds the current FEC block, so a single
// packet of a later block arriving before the current block completes makes it drop the
// current frame, and the stragglers that arrive a moment later are rejected as "behind".
// Every handoff then costs an RFI/IDR (a visible stutter) even though the data arrived.
//
// While the current block is incomplete, hold packets for later blocks for up to
// FROGTALE_REORDER_MS (default 80, 0 = stock behaviour) so stragglers can complete it first.
// In-order traffic is never delayed. Each hold is logged to FROGTALE_REORDER_LOG
// (default $XDG_CACHE_HOME/frogtale-reorder.log) as: epoch_ms outcome held_ms packets frame.
#define REORDER_MAX_HELD 4096

typedef struct _HELD_PACKET {
    char* buffer;
    int length;
} HELD_PACKET;

static HELD_PACKET heldPackets[REORDER_MAX_HELD];
static int heldCount;
static uint64_t holdStartUs;
static uint32_t holdStartFrame;
static int reorderHoldMs;
static int reorderBufferOffset;
static FILE* reorderLog;
static struct {
    uint32_t holds, resolved, timedOut, overflowed;
    uint64_t maxResolvedUs;
} reorderStats;

// Wall clock, so holds can be lined up with Starlink's :12/:27/:42/:57 handoff schedule.
static uint64_t epochMillis(void) {
#ifdef _WIN32
    FILETIME ft;
    GetSystemTimeAsFileTime(&ft);
    uint64_t t = ((uint64_t)ft.dwHighDateTime << 32) | ft.dwLowDateTime;
    return t / 10000 - 11644473600000ULL;
#else
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000 + tv.tv_usec / 1000;
#endif
}

// FrogtaleTV patch: NACK lost video packets so a patched host (aesse94/Apollo) resends them.
// The hold above alone can't help on Starlink because the stalled packets are lost, not late;
// with FROGTALE_NACK=1 every jump in RTP sequence numbers is reported as "FTNK" + ranges on the
// video socket, and the hold keeps the frame open (150 ms default) while the resends arrive.
static bool nackEnabled;
static bool nackHaveSeq;
static uint16_t nackHighestSeq;
static LC_SOCKADDR nackAddr;
static uint32_t nackRanges, nackPackets, nackRetries;
static int nackRetryMs;

// Received-sequence bitmap, so a NACK can be repeated for whatever is still missing. GeForce Now
// retries up to 3 times (rtpNackMaxRetries); one lost NACK or resend otherwise costs an IDR.
#define NACK_MAX_OUTSTANDING 32
#define NACK_MAX_RETRIES 2
static uint8_t nackSeen[65536 / 8];
static struct {
    uint16_t first, length;
    uint64_t sentUs;
    int retries;
} nackOutstanding[NACK_MAX_OUTSTANDING];
static int nackOutstandingCount;

#define NACK_SEEN(seq) (nackSeen[(seq) >> 3] & (1 << ((seq) & 7)))
#define NACK_MARK(seq) (nackSeen[(seq) >> 3] |= (1 << ((seq) & 7)))
#define NACK_CLEAR(seq) (nackSeen[(seq) >> 3] &= ~(1 << ((seq) & 7)))

static void nackSend(uint16_t first, uint16_t length) {
    // "FTNK", uint16 count, then count x (uint16 first, uint16 length), little endian
    unsigned char msg[4 + 2 + 4] = { 'F', 'T', 'N', 'K', 1, 0 };
    msg[6] = first & 0xFF;
    msg[7] = first >> 8;
    msg[8] = length & 0xFF;
    msg[9] = length >> 8;
    sendto(rtpSocket, (char*)msg, sizeof(msg), 0, (struct sockaddr*)&nackAddr, AddrLen);
    nackRanges++;
    nackPackets += length;
}

static void nackTrack(uint16_t first, uint16_t length) {
    if (nackOutstandingCount == NACK_MAX_OUTSTANDING) {
        // Drop the oldest; it is the least likely to still matter
        memmove(&nackOutstanding[0], &nackOutstanding[1], sizeof(nackOutstanding[0]) * (NACK_MAX_OUTSTANDING - 1));
        nackOutstandingCount--;
    }
    nackOutstanding[nackOutstandingCount].first = first;
    nackOutstanding[nackOutstandingCount].length = length;
    nackOutstanding[nackOutstandingCount].sentUs = PltGetMicroseconds();
    nackOutstanding[nackOutstandingCount].retries = 0;
    nackOutstandingCount++;
}

// Re-request whatever is still missing from earlier NACKs, every nackRetryMs, up to
// NACK_MAX_RETRIES times. Ranges that are complete or exhausted are dropped.
static void nackRetry(void) {
    static uint64_t lastCheckUs;
    uint64_t now = PltGetMicroseconds();
    if (now - lastCheckUs < 5000) {
        return;
    }
    lastCheckUs = now;

    int kept = 0;
    for (int i = 0; i < nackOutstandingCount; i++) {
        bool missing = false;
        for (uint16_t j = 0; j < nackOutstanding[i].length && !missing; j++) {
            missing = !NACK_SEEN(U16(nackOutstanding[i].first + j));
        }
        if (!missing) {
            continue;
        }
        if (now - nackOutstanding[i].sentUs >= (uint64_t)nackRetryMs * 1000) {
            if (nackOutstanding[i].retries >= NACK_MAX_RETRIES) {
                continue;
            }
            // Resend only the sub-ranges that are still missing
            uint16_t runStart = 0, runLength = 0;
            for (uint16_t j = 0; j <= nackOutstanding[i].length; j++) {
                uint16_t seq = U16(nackOutstanding[i].first + j);
                if (j < nackOutstanding[i].length && !NACK_SEEN(seq)) {
                    if (runLength++ == 0) {
                        runStart = seq;
                    }
                }
                else if (runLength > 0) {
                    nackSend(runStart, runLength);
                    runLength = 0;
                }
            }
            nackOutstanding[i].sentUs = now;
            nackOutstanding[i].retries++;
            nackRetries++;
        }
        nackOutstanding[kept++] = nackOutstanding[i];
    }
    nackOutstandingCount = kept;
}

static void nackObserve(char* buffer) {
    uint16_t seq = ((PRTP_PACKET)buffer)->sequenceNumber;
    if (!nackHaveSeq) {
        memset(nackSeen, 0, sizeof(nackSeen));
        nackHighestSeq = seq;
        nackHaveSeq = true;
        NACK_MARK(seq);
        return;
    }
    if (isBefore16(nackHighestSeq, seq)) {
        // Forget the bits half a sequence space ahead so the bitmap never reports stale packets
        for (uint16_t s = U16(nackHighestSeq + 1); s != U16(seq + 1); s = U16(s + 1)) {
            NACK_CLEAR(U16(s + 32768));
            NACK_CLEAR(s);
        }
        uint16_t missing = U16(seq - nackHighestSeq - 1);
        if (missing > 0 && missing <= 1024) {
            nackSend(U16(nackHighestSeq + 1), missing);
            nackTrack(U16(nackHighestSeq + 1), missing);
        }
        nackHighestSeq = seq;
    }
    NACK_MARK(seq);
}

static void reorderInit(int bufferOffset) {
    const char* nack = getenv("FROGTALE_NACK");
    nackEnabled = nack != NULL && atoi(nack) != 0;
    nackHaveSeq = false;
    nackRanges = nackPackets = nackRetries = 0;
    nackOutstandingCount = 0;
    const char* retry = getenv("FROGTALE_NACK_RETRY_MS");
    nackRetryMs = retry ? atoi(retry) : 35;
    memcpy(&nackAddr, &RemoteAddr, sizeof(nackAddr));
    SET_PORT(&nackAddr, VideoPortNumber);

    const char* ms = getenv("FROGTALE_REORDER_MS");
    // GeForce Now waits up to 68 ms for a frame (rtpQueueMaxFrameWaitDurationMs) with a ~35 ms
    // RTT; over Starlink to a home host the RTT is ~65 ms and NACKed frames completed in 47-83 ms.
    reorderHoldMs = ms ? atoi(ms) : (nackEnabled ? 100 : 80);
    reorderBufferOffset = bufferOffset;
    heldCount = 0;
    memset(&reorderStats, 0, sizeof(reorderStats));

    const char* path = getenv("FROGTALE_REORDER_LOG");
    char defaultPath[512];
    if (path == NULL) {
        const char* cache = getenv("XDG_CACHE_HOME");
        snprintf(defaultPath, sizeof(defaultPath), "%s/frogtale-reorder.log", cache ? cache : "/tmp");
        path = defaultPath;
    }
    reorderLog = fopen(path, "a");
    if (reorderLog != NULL) {
        setvbuf(reorderLog, NULL, _IOLBF, 0);
        fprintf(reorderLog, "%llu start hold_ms=%d nack=%d\n", (unsigned long long)epochMillis(), reorderHoldMs, nackEnabled);
    }
    Limelog("FrogtaleTV reorder hold: %d ms, NACK %s\n", reorderHoldMs, nackEnabled ? "on" : "off");
}

// <0 behind the block the queue is assembling, 0 that block, >0 a later block.
static int compareToCurrentBlock(char* buffer, int length) {
    PRTP_PACKET packet = (PRTP_PACKET)buffer;
    int dataOffset = sizeof(*packet) + ((packet->header & FLAG_EXTENSION) ? 4 : 0);
    if (length < dataOffset + (int)sizeof(NV_VIDEO_PACKET)) {
        // RtpvAddPacket() rejects these anyway; never hold them.
        return 0;
    }

    PNV_VIDEO_PACKET nvPacket = (PNV_VIDEO_PACKET)(buffer + dataOffset);
    int16_t frameDelta = (int16_t)U16(LE32(nvPacket->frameIndex) - rtpQueue.currentFrameNumber);
    if (frameDelta != 0) {
        return frameDelta;
    }
    return (int)((nvPacket->multiFecBlocks >> 4) & 0x3) - (int)rtpQueue.multiFecCurrentBlockNumber;
}

static void submitPacket(char* buffer, int length) {
    if (RtpvAddPacket(&rtpQueue, (PRTP_PACKET)buffer, length,
                      (PRTPV_QUEUE_ENTRY)&buffer[reorderBufferOffset]) != RTPF_RET_QUEUED) {
        free(buffer);
    }
}

static void logHold(const char* outcome, uint64_t heldUs, int packets) {
    if (reorderLog != NULL) {
        fprintf(reorderLog, "%llu %s %u %d %u\n", (unsigned long long)epochMillis(), outcome,
                (unsigned int)(heldUs / 1000), packets, holdStartFrame);
    }
}

// Release every held packet the queue can now take, in arrival order. With force, release
// all of them, which reproduces stock behaviour (the incomplete block is dropped).
static void reorderDrain(bool force) {
    bool progress;
    do {
        progress = false;
        int kept = 0;
        for (int i = 0; i < heldCount; i++) {
            if (force || compareToCurrentBlock(heldPackets[i].buffer, heldPackets[i].length) <= 0) {
                submitPacket(heldPackets[i].buffer, heldPackets[i].length);
                progress = true;
            }
            else {
                heldPackets[kept++] = heldPackets[i];
            }
        }
        heldCount = kept;
    } while (progress && heldCount > 0);
}

static void reorderProcess(char* buffer, int length) {
    if (nackEnabled) {
        nackObserve(buffer);
    }

    if (reorderHoldMs <= 0) {
        submitPacket(buffer, length);
        return;
    }

    if (compareToCurrentBlock(buffer, length) <= 0) {
        submitPacket(buffer, length);
        if (heldCount > 0) {
            int before = heldCount;
            reorderDrain(false);
            if (heldCount == 0) {
                uint64_t heldUs = PltGetMicroseconds() - holdStartUs;
                reorderStats.resolved++;
                if (heldUs > reorderStats.maxResolvedUs) {
                    reorderStats.maxResolvedUs = heldUs;
                }
                logHold("resolved", heldUs, before);
            }
        }
        return;
    }

    if (heldCount == REORDER_MAX_HELD) {
        reorderStats.overflowed++;
        logHold("overflow", PltGetMicroseconds() - holdStartUs, heldCount);
        reorderDrain(true);
        submitPacket(buffer, length);
        return;
    }

    if (heldCount == 0) {
        holdStartUs = PltGetMicroseconds();
        holdStartFrame = rtpQueue.currentFrameNumber;
        reorderStats.holds++;
    }
    heldPackets[heldCount].buffer = buffer;
    heldPackets[heldCount].length = length;
    heldCount++;
}

static void reorderCheckTimeout(void) {
    if (nackEnabled && nackOutstandingCount > 0) {
        nackRetry();
    }

    if (heldCount > 0) {
        uint64_t heldUs = PltGetMicroseconds() - holdStartUs;
        if (heldUs >= (uint64_t)reorderHoldMs * 1000) {
            reorderStats.timedOut++;
            logHold("timeout", heldUs, heldCount);
            reorderDrain(true);
        }
    }
}

static void reorderCleanup(void) {
    for (int i = 0; i < heldCount; i++) {
        free(heldPackets[i].buffer);
    }
    heldCount = 0;
    if (reorderLog != NULL) {
        fprintf(reorderLog, "%llu end holds=%u resolved=%u timeout=%u overflow=%u max_resolved_ms=%u nack_ranges=%u nack_packets=%u nack_retries=%u\n",
                (unsigned long long)epochMillis(), reorderStats.holds, reorderStats.resolved,
                reorderStats.timedOut, reorderStats.overflowed,
                (unsigned int)(reorderStats.maxResolvedUs / 1000), nackRanges, nackPackets, nackRetries);
        fclose(reorderLog);
        reorderLog = NULL;
    }
}

static void VideoReceiveThreadProc(void* context) {
    int err;
    int bufferSize, receiveSize, decryptedSize, minSize;
    char* buffer;
    char* encryptedBuffer;
    bool useSelect;
    int waitingForVideoMs;
    bool encrypted;

    encrypted = !!(EncryptionFeaturesEnabled & SS_ENC_VIDEO);
    decryptedSize = StreamConfig.packetSize + MAX_RTP_HEADER_SIZE;
    minSize = sizeof(RTP_PACKET) + ((EncryptionFeaturesEnabled & SS_ENC_VIDEO) ? sizeof(ENC_VIDEO_HEADER) : 0);
    receiveSize = decryptedSize + ((EncryptionFeaturesEnabled & SS_ENC_VIDEO) ? sizeof(ENC_VIDEO_HEADER) : 0);
    bufferSize = decryptedSize + sizeof(RTPV_QUEUE_ENTRY);
    buffer = NULL;

    if (setNonFatalRecvTimeoutMs(rtpSocket, UDP_RECV_POLL_TIMEOUT_MS) < 0) {
        // SO_RCVTIMEO failed, so use select() to wait
        useSelect = true;
    }
    else {
        // SO_RCVTIMEO timeout set for recv()
        useSelect = false;
    }

    // Allocate a staging buffer to use for each received packet
    if (encrypted) {
        encryptedBuffer = (char*)malloc(receiveSize);
        if (encryptedBuffer == NULL) {
            Limelog("Video Receive: malloc() failed\n");
            ListenerCallbacks.connectionTerminated(-1);
            return;
        }
    }
    else {
        encryptedBuffer = NULL;
    }

    reorderInit(decryptedSize);

    // While holding, the timeout is only checked when recv() returns. During a link stall nothing
    // arrives, so with the stock 100 ms poll a hold overran to ~180 ms. Poll faster when holding.
    int pollMs = UDP_RECV_POLL_TIMEOUT_MS;
    if (reorderHoldMs > 0 && !useSelect && setNonFatalRecvTimeoutMs(rtpSocket, 10) == 0) {
        pollMs = 10;
    }

    waitingForVideoMs = 0;
    while (!PltIsThreadInterrupted(&receiveThread)) {
        PRTP_PACKET packet;

        reorderCheckTimeout();

        if (buffer == NULL) {
            buffer = (char*)malloc(bufferSize);
            if (buffer == NULL) {
                Limelog("Video Receive: malloc() failed\n");
                ListenerCallbacks.connectionTerminated(-1);
                break;
            }
        }

        err = recvUdpSocket(rtpSocket,
                            encrypted ? encryptedBuffer : buffer,
                            receiveSize,
                            useSelect);
        if (err < 0) {
            Limelog("Video Receive: recvUdpSocket() failed: %d\n", (int)LastSocketError());
            ListenerCallbacks.connectionTerminated(LastSocketFail());
            break;
        }
        else if  (err == 0) {
            if (!receivedDataFromPeer) {
                // If we wait many seconds without ever receiving a video packet,
                // assume something is broken and terminate the connection.
                waitingForVideoMs += pollMs;
                if (waitingForVideoMs >= FIRST_FRAME_TIMEOUT_SEC * 1000) {
                    Limelog("Terminating connection due to lack of video traffic\n");
                    ListenerCallbacks.connectionTerminated(ML_ERROR_NO_VIDEO_TRAFFIC);
                    break;
                }
            }

            // Receive timed out; try again
            continue;
        }

        if (!receivedDataFromPeer) {
            receivedDataFromPeer = true;
            Limelog("Received first video packet after %d ms\n", waitingForVideoMs);

            firstDataTimeMs = PltGetMillis();
        }

#ifndef LC_FUZZING
        if (!receivedFullFrame) {
            if (PltGetMillis() - firstDataTimeMs >= FIRST_FRAME_TIMEOUT_SEC * 1000) {
                Limelog("Terminating connection due to lack of a successful video frame\n");
                ListenerCallbacks.connectionTerminated(ML_ERROR_NO_VIDEO_FRAME);
                break;
            }
        }
#endif

        if (err < minSize) {
            // Runt packet
            continue;
        }

        // Decrypt the packet into the buffer if encryption is enabled
        if (encrypted) {
            PENC_VIDEO_HEADER encHeader = (PENC_VIDEO_HEADER)encryptedBuffer;

            // If this frame is below our current frame number, discard it before decryption
            // to save CPU cycles decrypting FEC shards for a frame we already reassembled.
            //
            // Since this is happening _before_ decryption, this packet is not trusted yet.
            // It's imperative that we do not mutate any state based on this packet until
            // after it has been decrypted successfully!
            //
            // It's possible for an attacker to inject a fake packet that has any value of
            // header fields they want, however this provides them no benefit because we will
            // simply drop said packet here (if it's below the current frame number) or it
            // will pass this check and be dropped during decryption (if contents is tampered)
            // or after decryption in the RTP queue (if it's a replay of a previous authentic
            // packet from the host).
            //
            // In short, an attacker spoofing this value via MITM or sending malicious values
            // impersonating the host from off-link doesn't gain them anything. If they have
            // a true MITM, they can DoS our connection by just dropping all our traffic, so
            // tampering with packets to fail this check doesn't accomplish anything they
            // couldn't already do. If they're not on-link, we just throw their malicious
            // traffic away (as mentioned in the paragraph above) and continue accepting
            // legitmate video traffic.
            if (encHeader->frameNumber && LE32(encHeader->frameNumber) < RtpvGetCurrentFrameNumber(&rtpQueue)) {
                continue;
            }

            if (!PltDecryptMessage(decryptionCtx, ALGORITHM_AES_GCM, 0,
                                   (unsigned char*)StreamConfig.remoteInputAesKey, sizeof(StreamConfig.remoteInputAesKey),
                                   encHeader->iv, sizeof(encHeader->iv),
                                   encHeader->tag, sizeof(encHeader->tag),
                                   ((unsigned char*)(encHeader + 1)), err - sizeof(ENC_VIDEO_HEADER), // The ciphertext is after the header
                                   (unsigned char*)buffer, &err)) {
                Limelog("Failed to decrypt video packet!\n");
                continue;
            }
        }

        // Convert fields to host byte-order
        packet = (PRTP_PACKET)&buffer[0];
        packet->sequenceNumber = BE16(packet->sequenceNumber);
        packet->timestamp = BE32(packet->timestamp);
        packet->ssrc = BE32(packet->ssrc);

        // The reorder stage owns the buffer from here: it either queues, holds or frees it.
        reorderProcess(buffer, err);
        buffer = NULL;
    }

    reorderCleanup();

    if (buffer != NULL) {
        free(buffer);
    }

    if (encryptedBuffer != NULL) {
        free(encryptedBuffer);
    }
}

void notifyKeyFrameReceived(void) {
    // Remember that we got a full frame successfully
    receivedFullFrame = true;
}

// Decoder thread proc
static void VideoDecoderThreadProc(void* context) {
    while (!PltIsThreadInterrupted(&decoderThread)) {
        VIDEO_FRAME_HANDLE frameHandle;
        PDECODE_UNIT decodeUnit;

        if (!LiWaitForNextVideoFrame(&frameHandle, &decodeUnit)) {
            return;
        }

        LiCompleteVideoFrame(frameHandle, VideoCallbacks.submitDecodeUnit(decodeUnit));
    }
}

// Read the first frame of the video stream
int readFirstFrame(void) {
    // All that matters is that we close this socket.
    // This starts the flow of video on Gen 3 servers.

    closeSocket(firstFrameSocket);
    firstFrameSocket = INVALID_SOCKET;

    return 0;
}

// Terminate the video stream
void stopVideoStream(void) {
    if (!receivedDataFromPeer) {
        Limelog("No video traffic was ever received from the host!\n");
    }

    VideoCallbacks.stop();

    // Wake up client code that may be waiting on the decode unit queue
    stopVideoDepacketizer();

    PltInterruptThread(&udpPingThread);
    PltInterruptThread(&receiveThread);
    if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
        PltInterruptThread(&decoderThread);
    }

    if (firstFrameSocket != INVALID_SOCKET) {
        shutdownTcpSocket(firstFrameSocket);
    }

    PltJoinThread(&udpPingThread);
    PltJoinThread(&receiveThread);
    if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
        PltJoinThread(&decoderThread);
    }

    if (firstFrameSocket != INVALID_SOCKET) {
        closeSocket(firstFrameSocket);
        firstFrameSocket = INVALID_SOCKET;
    }
    if (rtpSocket != INVALID_SOCKET) {
        closeSocket(rtpSocket);
        rtpSocket = INVALID_SOCKET;
    }

    VideoCallbacks.cleanup();
}

// Start the video stream
int startVideoStream(void* rendererContext, int drFlags) {
    int err;

    firstFrameSocket = INVALID_SOCKET;

    // This must be called before the decoder thread starts submitting
    // decode units
    LC_ASSERT(NegotiatedVideoFormat != 0);
    err = VideoCallbacks.setup(NegotiatedVideoFormat, StreamConfig.width,
        StreamConfig.height, StreamConfig.fps, rendererContext, drFlags);
    if (err != 0) {
        return err;
    }

    rtpSocket = bindUdpSocket(RemoteAddr.ss_family, &LocalAddr, AddrLen,
                              RTP_RECV_PACKETS_BUFFERED * (StreamConfig.packetSize + MAX_RTP_HEADER_SIZE),
                              SOCK_QOS_TYPE_VIDEO);
    if (rtpSocket == INVALID_SOCKET) {
        VideoCallbacks.cleanup();
        return LastSocketError();
    }

    VideoCallbacks.start();

    err = PltCreateThread("VideoRecv", VideoReceiveThreadProc, NULL, &receiveThread);
    if (err != 0) {
        VideoCallbacks.stop();
        closeSocket(rtpSocket);
        VideoCallbacks.cleanup();
        return err;
    }

    if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
        err = PltCreateThread("VideoDec", VideoDecoderThreadProc, NULL, &decoderThread);
        if (err != 0) {
            VideoCallbacks.stop();
            PltInterruptThread(&receiveThread);
            PltJoinThread(&receiveThread);
            closeSocket(rtpSocket);
            VideoCallbacks.cleanup();
            return err;
        }
    }

    if (AppVersionQuad[0] == 3) {
        // Connect this socket to open port 47998 for our ping thread
        firstFrameSocket = connectTcpSocket(&RemoteAddr, AddrLen,
                                            FIRST_FRAME_PORT, FIRST_FRAME_TIMEOUT_SEC);
        if (firstFrameSocket == INVALID_SOCKET) {
            VideoCallbacks.stop();
            stopVideoDepacketizer();
            PltInterruptThread(&receiveThread);
            if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
                PltInterruptThread(&decoderThread);
            }
            PltJoinThread(&receiveThread);
            if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
                PltJoinThread(&decoderThread);
            }
            closeSocket(rtpSocket);
            VideoCallbacks.cleanup();
            return LastSocketError();
        }
    }

    // Start pinging before reading the first frame so GFE knows where
    // to send UDP data
    err = PltCreateThread("VideoPing", VideoPingThreadProc, NULL, &udpPingThread);
    if (err != 0) {
        VideoCallbacks.stop();
        stopVideoDepacketizer();
        PltInterruptThread(&receiveThread);
        if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
            PltInterruptThread(&decoderThread);
        }
        PltJoinThread(&receiveThread);
        if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
            PltJoinThread(&decoderThread);
        }
        closeSocket(rtpSocket);
        if (firstFrameSocket != INVALID_SOCKET) {
            closeSocket(firstFrameSocket);
            firstFrameSocket = INVALID_SOCKET;
        }
        VideoCallbacks.cleanup();
        return err;
    }

    if (AppVersionQuad[0] == 3) {
        // Read the first frame to start the flow of video
        err = readFirstFrame();
        if (err != 0) {
            stopVideoStream();
            return err;
        }
    }

    return 0;
}

const RTP_VIDEO_STATS* LiGetRTPVideoStats(void) {
    return &rtpQueue.stats;
}
