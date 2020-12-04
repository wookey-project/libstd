#include "autoconf.h"
#include "libc/signal.h"
#include "libc/time.h"
#include "libc/errno.h"
#include "libc/list.h"
#include "libc/semaphore.h"
#include "errno.h"

/* FIXME: get_current_ctx_id() should not be there */
#include "arch/cores/armv7-m/m4_syscall.h"

#ifdef CONFIG_STD_POSIX_TIMER

/*
 * 5 timers max per task
 */
#define STD_POSIX_TIMER_MAXNUM 5

uint32_t timer_mutex = 1;

typedef struct {
    void (*sigev_notify_function)(__sigval_t);
    bool set;               /* is timer active (timer_settime() has been executed at least once with
                               non-null it_value content */
    bool postponed;         /* timer has been postponed by another timer_settime(). A new node has been created.
                               for this node, the timer_handler() should not call the notify function. */


} timer_infos_t;

list_t timer_list;

/* timer handler that is effectively called by the kernel */
void timer_handler(uint32_t ms)
{
    /* when coming back from the kernel, we don't have the timer key with us. To be sure to get
     * back the correct timer node, each time we call the sys_alarm() */
    ms = ms;
}

/* zeroify function, called at task preinit.*/
void timer_initialize(void)
{
    list_create(STD_POSIX_TIMER_MAXNUM, &timer_list);
}




/*
 * Create a timer (timer is not activated here).
 */
int timer_create(clockid_t clockid, struct sigevent *sevp, timer_t *timerid)
{
    mbed_error_t errcode = 0;
    uint8_t ret;

    /* by now, CLOCK_REALTIME not supported */
    if (clockid == CLOCK_REALTIME) {
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }
    /* other input params sanitation */
    if (clockid != CLOCK_MONOTONIC || sevp == NULL || timerid == NULL) {
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }
    /* by now, SIGEV_SIGNAL is not supported */
    if (sevp->sigev_notify == SIGEV_SIGNAL) {
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }
    /* other input params sanitation */
    if (sevp->sigev_notify != SIGEV_THREAD && sevp->sigev_notify != SIGEV_NONE) {
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }
    /* SIGEV_THREAD case: check notify function */
    if (sevp->sigev_notify == SIGEV_THREAD && sevp->sigev_notify_function == NULL) {
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }
    /* timer identifier is the current cycle id. To avoid collision in case ot SMP
     * system, we use a semaphore to lock a shared ressource between getting current
     * timestamp, then unlock the semaphore. Doing this, even in SMP systems, concurrent
     * timer_create() will have separated timer_id.
     */
    if (get_current_ctx_id() == CTX_ISR) {
        /* ISR thread: trying nonblocking lock... */
        if (mutex_trylock(&timer_mutex) == false) {
            /* didn't manage to get mutex lock without blocking (another thread is blocking it ?) */
            errcode = -1;
            __libstd_set_errno(EAGAIN);
            goto err;
        }
    } else {
        mutex_lock(&timer_mutex);
    }
    ret = sys_get_systick(timerid, PREC_CYCLE);
    if (ret != SYS_E_DONE) {
        /* calling task must be allowed to measure cycle-level timestamping */
        errcode = -1;
        __libstd_set_errno(EPERM);
        goto err;
    }
    mutex_unlock(&timer_mutex);

err:
    return errcode;
}

/*
 * Activate timer
 */
#if 0
int timer_settime(timer_t timerid, int flags, const struct itimerspec *new_value, struct itimerspec *old_value)
{
    return 0;
}

int timer_gettime(timer_t timerid, struct itimerspec *curr_value)
{
    return 0;
}
#endif

#endif
