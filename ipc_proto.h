#ifndef IPC_H_
#define IPC_H_

/* IPC based synchronization toolkit */

#include "api/types.h"

/*
 * generic synchronization specific binary IPC API
 */
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
    /** Full authentication phase request */
    MAGIC_CRYPTO_AUTH_CMD    = 0x68,
    /** DMA 'buffer ready' command and response */
    MAGIC_DMA_BUF_READY_CMD  = 0x72,
    MAGIC_DMA_BUF_READY_RESP = 0x73,
    /** settigs magics */
    MAGIC_SETTINGS_CMD       = 0x90,
    MAGIC_SETTINGS_LOCK      = 0x91,
    /** USB vs storage synchronization control plane */
    MAGIC_STORAGE_SCSI_BLOCK_SIZE_CMD = 0x82,
    MAGIC_STORAGE_SCSI_BLOCK_SIZE_RESP = 0x83,
    MAGIC_STORAGE_SCSI_BLOCK_NUM_CMD  = 0x84,
    MAGIC_STORAGE_SCSI_BLOCK_NUM_RESP  = 0x85,
    MAGIC_STORAGE_EJECTED = 0x86,
    /** finishing with invalid */
    MAGIC_INVALID            = 0xff,
};

enum sync_init_state {
    SYNC_READY        = 0,
    SYNC_ASK_FOR_DATA = 1,
    SYNC_WAIT         = 2,
    SYNC_DONE         = 3,
    SYNC_ACKNOWLEDGE  = 4,
    SYNC_UNKNOWN      = 5,
    SYNC_FAILURE      = 6
};

/* Smart vs Pin structure, mapped in data.u8 */
enum sc_field_type {
    SC_USER_PIN = 1,
    SC_PET_PIN  = 2,
    SC_PET_NAME = 3
};

enum sc_field_request {
    SC_REQ_AUTHENTICATE = 1,
    SC_REQ_MODIFY       = 2
};

typedef struct {
    enum sc_field_type sc_type;
    enum sc_field_request sc_req;
    char sc_petname[24];
} t_sc_request;

/**/
union data_block {
    uint8_t u8[32];
    uint32_t u32[8];
    uint16_t u16[16];
    t_sc_request req;
};




struct sync_command {
    uint8_t magic;
    uint8_t state;
} __attribute__((packed));

struct sync_command_data {
    uint8_t          magic;
    uint8_t          state;
    uint8_t          data_size;
    union data_block data;
} __attribute__((packed));

/*
 * Dataplane specific IPC commands
 * This define the SCSI based communication protocol for requiring read/write
 * commands between tasks
 */

enum dataplane_magic {
  DATA_WR_DMA_REQ = 0x01,
  DATA_WR_DMA_ACK = 0x02,
  DATA_RD_DMA_REQ = 0x03,
  DATA_RD_DMA_ACK = 0x04,
  /** finishing with invalid */
  DATA_INVALID    = 0xff,
};

struct dataplane_command {
    uint8_t  magic;
    uint32_t sector_address;
    uint32_t num_sectors;
};

typedef union {
    struct  dataplane_command dataplane_cmd;
    struct  sync_command      sync_cmd;
    struct  sync_command_data sync_cmd_data;
    uint8_t                   magic; // first field of the two above
} t_ipc_command;


#endif /*! IPC_H_*/
