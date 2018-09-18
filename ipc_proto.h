#ifndef IPC_H_
#define IPC_H_

/* IPC based synchronization toolkit */

#include "api/types.h"

enum sync_magic {
    /** task state request command and response */
    MAGIC_TASK_STATE_CMD     = 0x42,
    MAGIC_TASK_STATE_RESP    = 0x43,
    /** cryptography interaction command and response */
    MAGIC_CRYPTO_INJECT_CMD  = 0x52,
    MAGIC_CRYPTO_INJECT_RESP = 0x53,
    /** cryptography interaction command and response */
    MAGIC_CRYPTO_PIN_CMD     = 0x62,
    MAGIC_CRYPTO_PIN_RESP    = 0x63,
    /** DMA 'buffer ready' command and response */
    MAGIC_DMA_BUF_READY_CMD  = 0x72,
    MAGIC_DMA_BUF_READY_RESP = 0x73,
};

enum sync_init_state {
    SYNC_READY        = 0,
    SYNC_ASK_FOR_DATA = 1,
    SYNC_WAIT         = 2,
    SYNC_DONE         = 3,
    SYNC_ACKNOWLEDGE  = 4,
    SYNC_UNKNOWN      = 5
};

struct sync_command {
    uint8_t magic;
    uint8_t state;
    uint8_t data_size;
    uint8_t data[32];
} __PACKED;

#endif /*! IPC_H_*/
