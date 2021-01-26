#include "autoconf.h"
#include "libc/signal.h"
#include "libc/time.h"
#include "libc/errno.h"
#include "libc/sync.h"
#include "libc/list.h"
#include "libc/nostd.h"
#include "libc/stdio.h"
#include "libc/semaphore.h"
#include "libc/string.h"
#include "errno.h"

/* FIXME: get_current_ctx_id() should not be there */
#include "arch/cores/armv7-m/m4_syscall.h"

#ifdef CONFIG_STD_POSIX_TIMER

#define TIME_DEBUG 0

/*
 * 5 timers max per task. By now EwoK only handle one timer at a time... :-/
 */
#define STD_POSIX_TIMER_MAXNUM 10

uint32_t timer_mutex = 1;

typedef struct {
    timer_t  id;            /* Timer identifier (uint64_t), set at timer creation time. differ from 'key', upgraded with next timer trigger timetstamp
                               MUST be aligned on 8 bytes to avoid strd usage fault (compiler bug) */
    uint32_t duration_ms;   /* duration in ms (at least for initial, it periodic) */
    sigev_notify_function_t sigev_notify_function;
    __sigval_t              sigev_value;
    int                     sigev_notify;  /* notify mode */
    bool                    set;  /* is timer active (timer_settime() has been executed at least once with
                               non-null it_value content */
    bool postponed;         /* timer has been postponed by another timer_settime(). A new node has been created.
                               for this node, the timer_handler() should not call the notify function. */
    bool periodic;          /* when setting a timer with it_interval, the timer is executed periodicaly until a new
                               timer_settime() reconfigure it. */
    struct timespec         period; /* period (interval) specification, is periodic == true */
} timer_infos_t;

list_t timer_list;
list_t unset_timer_list;

uint8_t dangling_timers;

void timer_handler(uint32_t ms);

/******************************************************************
 * Local static utility functions, that interact with list backend
 */

/*
 * Create a new timer node using the given key as timer identifier
 */
static int timer_create_node(struct sigevent *sevp, timer_t key, bool periodic)
{
    int errcode = 0;

    /* create an unset timer node in the list of timers. There is two main differences between
     * unset timers and set timers:
     * 1. the key used by unset timers is the full systick time of the timer_create() (not trunkated
     *    at milisecond multiple)
     * 2. The set flag is set at false.
     *
     * Timer id is also used for the node identifier (node->data->id).
     */
    timer_infos_t* info = NULL;

    if (wmalloc((void**)&info, sizeof(timer_infos_t), ALLOC_NORMAL) != 0) {
        errcode = -1;
        __libstd_set_errno(ENOMEM);
        goto err;
    }

    info->sigev_notify_function = sevp->sigev_notify_function;
    info->sigev_value = sevp->sigev_value;
    info->sigev_notify = sevp->sigev_notify;
    info->id = key;
    //memcpy(&info->id, &key, sizeof(uint64_t));
    info->set = false;
    info->postponed = false;
    info->periodic = periodic;
    info->duration_ms = 0;

#if TIME_DEBUG
    printf("creating timer with id:\n");
    hexdump((uint8_t*)&key, 8);
#endif

    switch (list_insert(&unset_timer_list, info, key)) {
        case MBED_ERROR_INVPARAM:
            /* should not happen */
            wfree((void**)&info);
            errcode = -1;
            __libstd_set_errno(EINVAL);
            goto err;
            break;
        case MBED_ERROR_BUSY:
            /* should not happen */
            wfree((void**)&info);
            errcode = -1;
            __libstd_set_errno(EAGAIN);
            goto err;
            break;
        case MBED_ERROR_NOMEM:
            wfree((void**)&info);
            errcode = -1;
            __libstd_set_errno(ENOMEM);
            goto err;
            break;
        default:
            break;
    }

err:
    return errcode;
}


/*
 * SetTime case: Set a node in a list (newly set or already set) and
 * handle alarm backend.
 */
int timer_setnode(timer_t id, const struct timespec *ts, bool interval, const struct timespec *interval_ts, struct itimerspec *old)
{
    int errcode = 0;
    uint8_t ret;
    timer_infos_t *info = NULL;
    /* 1. get back timer node based on key...  */
    struct list_node *node = unset_timer_list.head;
    /* foreach node, get back its id....
     * As we have locked the timer lock, we can read the list manualy here */

    /*calculating new key */
    uint64_t key;
    ret = sys_get_systick(&key, PREC_MICRO);
    if (ret != SYS_E_DONE) {
        /* calling task must be allowed to measure cycle-level timestamping */
        errcode = -1;
        __libstd_set_errno(EPERM);
        goto err;
    }
    /* key is in milisecond */
    uint32_t period_ms = 0;
    period_ms = (ts->tv_sec * 1000);
    period_ms += (ts->tv_nsec / 1000000);
    /* key is in us to avoid collision */
    key += (period_ms*1000);

#if TIME_DEBUG
    printf("searching timer with id in unset list:\n");
    hexdump((uint8_t*)&id, 8);
#endif
    /* searching for node.... */
    while (node != NULL) {
        //if (memcmp(&((timer_infos_t*)node->data)->id, &id, sizeof(uint64_t)) == 0) {
        if (((timer_infos_t*)node->data)->id == id) {
            break;
        }
        node = node->next;
    }
    if (node == NULL) {
        /* timer not found in unset. Is it already set ? */
        goto timer_set;
    }

    /* handling unset timers */

    if (period_ms == 0) {
        /* unsetting a previously alread not set timer has no meaning... */
        goto err;
    }

    /* for unset timers, if old, exists, set it with zeros */
    if (old) {
        old->it_value.tv_sec = 0;
        old->it_value.tv_nsec = 0;
        old->it_interval.tv_sec = 0;
        old->it_interval.tv_nsec = 0;
    }

    /* simple case: timer is not yet set, update, and re-insert with alarm launched */
    /*@ assert \valid(node); */
    info = (timer_infos_t*)node->data;

    /* We can remove the node without risk. Should not fail  */
    list_remove(&unset_timer_list, (void**)&info, node->key);

    /* update node infos */
    info->set = true;
    info->duration_ms = period_ms;

    if (interval == true) {
        info->periodic = true;
        if (interval_ts) {
            info->period.tv_sec = interval_ts->tv_sec;
            info->period.tv_nsec = interval_ts->tv_nsec;
        }
    }

    /* and add it back with new key */
    if ((ret = list_insert(&timer_list, info, key)) != MBED_ERROR_NONE) {
        wfree((void**)&info);
        errcode = -1;
        __libstd_set_errno(ENOMEM);
        goto err;
    }
    /* finished, we can call kernel alarm */
    if (info->sigev_notify != SIGEV_THREAD) {
        /* no thread to notify */
        goto err;
    }
    goto call_alarm;

timer_set:
#if TIME_DEBUG
    printf("... not found. searching in set list.\n");
#endif
    node = timer_list.head;
    while (node != NULL) {
        //if (memcmp(&((timer_infos_t*)node->data)->id, &id, sizeof(uint64_t)) == 0) {
        if (((timer_infos_t*)node->data)->id == id) {
            break;
        }
        node = node->next;
    }
    if (node == NULL) {
        /* not in timer_list neither... not found then*/
#if TIME_DEBUG
        printf("timer not found in set timers\n");
#endif
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }
    info = (timer_infos_t*)node->data;

    /* when timer already set and 'old' is non-null, set the previously
     * configured values to it */
    if (old) {
        old->it_value.tv_sec = info->duration_ms / 1000;
        old->it_value.tv_nsec = (info->duration_ms  % 1000) * 1000000;
        if (info->periodic == false) {
            old->it_interval.tv_sec = 0;
            old->it_interval.tv_nsec = 0;
        } else {
            old->it_interval.tv_sec = info->period.tv_sec;
            old->it_interval.tv_nsec = info->period.tv_nsec;
        }
    }


    /* 3. the node is already set*/
    /* for all nodes having the same id (including that one),
     * mark them as 'postponed'. */
    info->postponed = true;
    while (node != NULL) {
        //if (memcmp(&((timer_infos_t*)node->data)->id, &id, sizeof(uint64_t)) == 0) {
        if (((timer_infos_t*)node->data)->id == id) {
            /* old timer configs, even if triggered by kernel, will
             * not execute upper hanlder, neither generate a new
             * timer period */
            ((timer_infos_t*)node->data)->postponed = true;
            ((timer_infos_t*)node->data)->periodic = false;
        }
        node = node->next;
    }
    if (period_ms == 0) {
        /* we require to set a node with NULL value, meaning cleaning a timer. Previous instances has been
         * postponed, we can leave now... */
        goto err;
    }
    /* all previously set nodes are set as postponed. When
     * corresponding alarm will be triggered by the kernel,
     * the handler will not execute upper handler. */
    /* create a new node for currently set timer */
    timer_infos_t *new_info = NULL;
    if (wmalloc((void**)&new_info, sizeof(timer_infos_t), ALLOC_NORMAL) != 0) {
        errcode = -1;
        __libstd_set_errno(ENOMEM);
        goto err;
    }
    new_info->sigev_notify_function = info->sigev_notify_function;
    new_info->sigev_value = info->sigev_value;
    new_info->sigev_notify = info->sigev_notify;
    new_info->id = info->id;
    //memcpy(&new_info->id, &info->id, sizeof(uint64_t));
    new_info->set = true;
    new_info->postponed = false;
    if (interval == true) {
        new_info->periodic = true;
    }
    /* insert the new node with the new key */
    if ((ret = list_insert(&timer_list, new_info, key)) != MBED_ERROR_NONE) {
        wfree((void**)&new_info);
        errcode = -1;
        __libstd_set_errno(ENOMEM);
        goto err;
    }
    /* finished, we can call kernel alarm */
    if (new_info->sigev_notify != SIGEV_THREAD) {
        /* no thread to notify */
        goto err;
    }

call_alarm:
    /* call sigalarm() */
    switch (sys_alarm(period_ms, timer_handler)) {
        case SYS_E_DONE:
            goto err;
        case SYS_E_DENIED:
            /* TODO: remove node */
            errcode = -1;
            __libstd_set_errno(EPERM);
            goto err;
            break;
        default:
            /* TODO: remove node */
            errcode = -1;
            __libstd_set_errno(EAGAIN);
            goto err;
            break;
    }

err:
    return errcode;
}



/* timer handler that is effectively called by the kernel */
void timer_handler(uint32_t ms)
{
    uint64_t key;
    mbed_error_t errcode;
    ms = ms;
    int ret;

    if (mutex_trylock(&timer_mutex) == false) {
        /* didn't manage to get mutex lock without blocking (another thread is blocking it ?) */
        set_u8_with_membarrier(&dangling_timers, dangling_timers + 1);
        goto err_nolock;
    }

    if (timer_list.size == 0) {
        /* this should **not** happen! */
        goto err;
    }
    struct list_node *node = timer_list.head;
    /*@ assert \valid(timer_list->head); */
    timer_infos_t *info = NULL;

    if (dangling_timers > 0) {
        /* one or more previously executed list accesses were locked by another thread.
         * This prevent the handler from properly accessing & removing the timer node.
         * In that case, for each such 'dangling' timer node, remove it here */
        if (timer_list.size < dangling_timers) {
            /* this should not happen, as only this function remove nodes */
            goto err;
        }
        for (uint8_t i = 0; i < dangling_timers; ++i) {
            errcode = list_remove(&timer_list, (void**)&info, timer_list.head->key);
            wfree((void**)&info);
            set_u8_with_membarrier(&dangling_timers, dangling_timers - 1);
        }
        /*@ assert dangling_timers == 0; */
        /* All dangling removed */
    }
    /* when coming back from the kernel, we don't have the timer key with us. To be sure to get
     * back the correct timer node, the ordered list of timer is using a timer timeout timestamp based
     * key to ensure an ordered listing.
     * As a consequence, when the handler is called, the terminated timer is **always** the first node of the list.
     */
    //memcpy(&key, &node->key, sizeof(uint64_t));
    key = node->key;

    /* remove from activated timer list */
    errcode = list_remove(&timer_list, (void**)&info, key);
    switch (errcode) {
        case MBED_ERROR_INVPARAM:
            /* should not happen here */
            goto err;
            break;
        case MBED_ERROR_NOSTORAGE:
            /* should not happen, checked before */
            goto err;
            break;
        case MBED_ERROR_BUSY:
            /* should not happen as timer lock is set */
            goto err;
            break;
        case MBED_ERROR_NOTFOUND:
            /* timer not found! */
            goto err;
            break;
        default:
            break;
    }

    struct sigevent sevp = { 0 };
    sevp.sigev_notify_function = info->sigev_notify_function;
    sevp.sigev_notify = info->sigev_notify;
    sevp.sigev_value = info->sigev_value;

    if (info->postponed == true) {

        /* the current timer node has been postponed. Another timer node exists (or has existed)
         * and has been/will be executed in order to execute the associated callback. By now,
         * just do nothing. */

        struct list_node *next_node = node;
        bool not_the_last = false;

        /* is there other future timers (postponed or not) for the same timer id ? */
        while (next_node && next_node->next) {
            next_node = next_node->next;
            if (((timer_infos_t*)(next_node->data))->id == info->id) {
                /* future timers with the same timer id will trig */
                not_the_last = true;
            }
        }
        if (not_the_last == false) {
            /* current postponed timer is the last one for this id, no more timer trigger. We push back the
             * timer id to the inactive timer list */
            if ((ret = timer_create_node(&sevp, info->id, false)) == -1) {
#if TIME_DEBUG
                printf("[handler] failed to rearm timer (creation)\n");
#endif
                wfree((void**)&info);
                goto err;
            }
        }
    } else {
        if (info->sigev_notify == SIGEV_THREAD) {
            /* upper thread execution is requested. The callback **must** be set as it has been checked
             * at creation time. */
            info->sigev_notify_function(info->sigev_value);

            if (info->periodic == true) {
                /* reinsert a new timer, by creating a new one with the same key.... */
                struct timespec ts = { 0 };

                ts.tv_nsec = info->period.tv_nsec;
                ts.tv_sec = info->period.tv_sec;

                if ((ret = timer_create_node(&sevp, info->id, true)) == -1) {
#if TIME_DEBUG
                    printf("[handler] failed to rearm timer (creation)\n");
#endif
                    wfree((void**)&info);
                    goto err;
                }
                if ((ret = timer_setnode(info->id, &ts, true, &info->period, NULL)) == -1) {
#if TIME_DEBUG
                    printf("[handler] failed to rearm timer (set)\n");
#endif
                    wfree((void**)&info);
                    goto err;
                }
            } else {
                /* not periodic, keep the timerid as created but not set for future timer_settime()  */
                if ((ret = timer_create_node(&sevp, info->id, false)) == -1) {
#if TIME_DEBUG
                    printf("[handler] failed to keep timer id (creation)\n");
#endif
                    wfree((void**)&info);
                    goto err;
                }
            }
        }
    }
    wfree((void**)&info);
err:
    mutex_unlock(&timer_mutex);
err_nolock:
    return;
}


/**************************************************************************
 * Exported functions part 1; timers
 */


/* zeroify function, called at task preinit.*/
void timer_initialize(void)
{
    list_create(STD_POSIX_TIMER_MAXNUM, &timer_list);
    list_create(STD_POSIX_TIMER_MAXNUM, &unset_timer_list);
#if TIME_DEBUG
    printf("timer list:\n");
    printf("max: %d\n", timer_list.max);
    printf("size: %d\n", timer_list.size);
    printf("head: %x\n", timer_list.head);
    printf("mutex: %x\n", timer_list.lock);
#endif
    dangling_timers = 0;
}



/*
 * Create a timer (timer is not activated here).
 */
int timer_create(clockid_t clockid, struct sigevent *sevp, timer_t *timerid)
{
    int errcode = 0;
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

    errcode = timer_create_node(sevp, *timerid, false);

    mutex_unlock(&timer_mutex);
err:
    return errcode;
}

/*
 * Activate timer
 *
 * At settime():
 * if the node set at create() time is not yet active:
 * - it is get back (using timerid==key)
 * - upgraded by setting the key properly with the new itimespec informations
 * - re-added correctly in the list accordingly
 * if the node set at create() time is already active (a previous create() has been done)
 * - all potential existing nodes are flagued as 'postponed' (the handler will not call the upper layer)
 * - a new node is created using the itimespec information and set in the list correctly (it may be **before** a previously postoned
 *   timer if the time is reduced
 *
 * The alarm request is sent to the kernel.
 */
int timer_settime(timer_t timerid, int flags __attribute__((unused)), const struct itimerspec *new_value, struct itimerspec *old_value __attribute__((unused)))
{
    int errcode = 0;
    const struct timespec *ts;
    bool interval = false;
    bool cleaning = false;

    /* Sanitize first. old_value is allowed to be NULL */
    if (new_value == NULL) {
        errcode = -1;
        __libstd_set_errno(EFAULT);
        goto err;
    }
    /* select type of setting (value or interval) */
    /*TODO: FIX1: if it_value fields are 0 -> unset timer */
    ts = &new_value->it_value;
    if (new_value->it_value.tv_sec == 0 && new_value->it_value.tv_nsec == 0) {
        /* simply clean previously set timer */
        cleaning = true;
    }
    /* if both interval and value are non-null, this is a periodic timer */
    if ((new_value->it_interval.tv_sec != 0 || new_value->it_interval.tv_nsec != 0) &&
        (new_value->it_value.tv_sec != 0 || new_value->it_value.tv_nsec != 0)) {
        /* an periodic interval is requested after first trigger (set by it_value)*/
        interval = true;
    }
    /* when not unsetting a timer, timer specs must be large enough */
    if (cleaning == false) {
        if (ts->tv_sec == 0 && ts->tv_nsec < 1000000) {
            /* too short timer step */
            errcode = -1;
            __libstd_set_errno(EINVAL);
            goto err;
        }
        if (ts->tv_nsec > 999999999) {
            /* nsec bigger than 1 sec (POSIX compliance) */
            errcode = -1;
            __libstd_set_errno(EINVAL);
            goto err;
        }
        if (interval == true && new_value->it_interval.tv_sec == 0 && new_value->it_interval.tv_nsec < 1000000) {
            /* too short interval */
            errcode = -1;
            __libstd_set_errno(EINVAL);
            goto err;
        }
    }

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

    errcode = timer_setnode(timerid, &new_value->it_value, interval, &new_value->it_interval, old_value);

    mutex_unlock(&timer_mutex);
err:
    return errcode;
}

int timer_gettime(timer_t timerid, struct itimerspec *curr_value)
{
    uint64_t timer_us;
    uint64_t now_us;
    uint64_t eta_us;
    int errcode = 0;
    timer_infos_t *info = NULL;
    struct list_node *node = NULL;
    uint8_t ret;
    /* Sanitize first */
    if (curr_value == NULL) {
        errcode = -1;
        __libstd_set_errno(EFAULT);
        goto err;
    }

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

    if (timer_list.size == 0) {
        /* no timer set */
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }

    node = timer_list.head;
    /*@ assert \valid(node);*/

    /* searching no set timers first */
    while (node != NULL) {
        info = node->data;
        //if (memcmp(&info->id, &timerid, sizeof(uint64_t)) == 0) {
        if (info->id == timerid) {
            if (&info->postponed == false) {
                break;
            }
        }
        node = node->next;
    }
    if (node == NULL) {
        /* timer not found. Is timer unset ? */
        node = unset_timer_list.head;
        while (node != NULL) {
            info = node->data;
        //    if (memcmp(&info->id, &timerid, sizeof(uint64_t)) == 0) {
            if (info->id == timerid) {
                break;
            }
            node = node->next;
        }
        if (node == NULL) {

            errcode = -1;
            __libstd_set_errno(EINVAL);
            goto err_lock;
        }
    }

    /*@ assert \valid(node); */
    /*@ assert \valid(info); */
    timer_us = info->id;

    if (info->set == false) {
        /* unset timer */
        curr_value->it_value.tv_sec = 0;
        curr_value->it_value.tv_nsec = 0;
        goto err_lock;
    }

    eta_us = (timer_us + (info->duration_ms*1000)) - now_us;
    /* timer id is the time (in us) when the timer has been set */
    //memcpy(&timer_us, &info->id, sizeof(uint64_t));
    timer_us = info->id;
    ret = sys_get_systick(&now_us, PREC_MICRO);
    if (ret != SYS_E_DONE) {
        /* calling task must be allowed to measure cycle-level timestamping */
        errcode = -1;
        __libstd_set_errno(EPERM);
        goto err;
    }
    if (info->periodic == true) {
            curr_value->it_interval.tv_nsec = (info->duration_ms % 1000) * 1000000;
            curr_value->it_interval.tv_sec = info->duration_ms / 1000;
    }
    curr_value->it_value.tv_nsec = (eta_us % 1000000) * 1000;
    curr_value->it_value.tv_sec = eta_us / 1000000;

err_lock:
    mutex_unlock(&timer_mutex);
err:
    return errcode;
}

/**************************************************************************
 * Exported functions part 1; clock
 */

#if 0
/* TODO or not TODO, that is the question... */
int clock_getres(clockid_t clockid, struct timespec *res)
{
    /* On Ework the precision of timers is in ms, depending on the
     * CONFIG_SCHED_PERIOD value for inccuracy. Usual scheduling period
     * is about 10 ms but can be more or less.
     */
}
#endif

int clock_gettime(clockid_t clockid, struct timespec *tp)
{
    int errcode = 0;
    uint64_t time;
    /* sanitation */
    if (tp == NULL) {
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }
    /* by now, no support for RTC clock. For boards with RTC clocks, add a config
     * option to allow CLOCK_REALTIME */
    if (clockid != CLOCK_MONOTONIC) {
        errcode = -1;
        __libstd_set_errno(EINVAL);
        goto err;
    }

    /* as we can't check the level of permission we have (depend on the task),
     * we first try the most precise measurement, and continue upto the less
     * precise one.
     * The first valid measurement makes the function returns */
    if (sys_get_systick(&time, PREC_MICRO) == SYS_E_DONE) {
        tp->tv_nsec = (time % 1000000) * 1000;
        tp->tv_sec = (time / 1000000);
        goto err;
    }
    if (sys_get_systick(&time, PREC_MILLI) == SYS_E_DONE) {
        tp->tv_nsec = (time % 1000) * 1000000;
        tp->tv_sec = (time / 1000);
        goto err;
    }

    /* EPERM is not a POSIX defined return value, but time measurement is controled on EwoK */
    errcode = -1;
    __libstd_set_errno(EPERM);
err:
    return errcode;
}


#endif
