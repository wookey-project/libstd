
#include "autoconf.h"
#include "libc/types.h"


typedef void (*zeroify_p)(void);



/*
 * Let's define services zeroficication prototypes
 */

#if CONFIG_STD_SYSV_MSQ
void msg_zeroify(void);
#endif
void init_ring_buffer(void);

/*
 * The zeroification vector definition
 */
static const zeroify_p glob_array[] = {
#if CONFIG_STD_SYSV_MSQ
    msg_zeroify,
#endif
    init_ring_buffer,
    NULL
};

/*
 * The zeroification handler at boot time
 */
void zeroify_libc_globals(void) {
    uint8_t i = 0;
    while (glob_array[i] != NULL) {
        glob_array[i]();
        i++;
    }
}
