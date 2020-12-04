
#include "autoconf.h"
#include "libc/types.h"


/*
 * Let's define services zeroficication prototypes
 */

#if CONFIG_STD_POSIX_SYSV_MSQ
void msg_zeroify(void);
#endif
#if CONFIG_STD_POSIX_TIMER
void timer_initialize(void);
#endif
void init_ring_buffer(void);

/*
 * The zeroification handler at boot time
 */
void zeroify_libc_globals(void) {
    init_ring_buffer();
#if CONFIG_STD_SYSV_MSQ
    msg_zeroify();
#endif
#if CONFIG_STD_POSIX_TIMER
    timer_initialize();
#endif
}
