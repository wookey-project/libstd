/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef TIME_H_
#define TIME_H_

#include "autoconf.h"
#include "libc/types.h"
#include "libc/signal.h"

typedef enum clockid {
    CLOCK_REALTIME = 0,
    CLOCK_MONOTONIC,
} clockid_t;

/* standard timer_t type (timer identifier) for embedded.
 * Correspond to current cycle */
typedef uint64_t timer_t;


/*
 * POSIX compliant timespec structure definition
 */
struct timespec {
    time_t tv_sec;        /* seconds */
    long   tv_nsec;       /* nanoseconds */
};

struct itimerspec {
    struct timespec it_interval;
    struct timespec it_value;
};

/*
 * POSIX-1 2001 and POSIX-1 2008 compliant sleep() implementation
 * TODO: errno is not set as not yet supported by libstd
 */
unsigned int sleep(unsigned int second);


/*
 * POSIX-1 2001 and POSIX-1 2008 compliant nanosleep() implementation
 * TODO: errno is not set as not yet supported by libstd
 */
int nanosleep(const struct timespec *req, struct timespec *rem);

#ifdef CONFIG_STD_POSIX_TIMER
/*
 * INFO: to work properly, timer API request the calling task to have full time measurement access (upto cycle level).
 * Create a new, unique, timer identifier associated to the specified clock id.
 * The timer behavior (polling, thread execution...) is specified in the sigevent structure.
 * This function does not activate the timer.
 */

int timer_create(clockid_t clockid, struct sigevent *sevp, timer_t *timerid);

/*
 * Activate or reconfigure timer (if already set) according to new_value. If old_value exists, previously set
 * configuration is returned in old_value.
 * If new_value->it_value is set to 0, the timer is unset
 * If new_value->it_interval is not set to 0, the timer is periodic, based on new_value->it_value values for interval duration
 * If new_value->it_interval is set to 0 as previously configured timer was periodic, the timer is no more periodic
 */
int timer_settime(timer_t timerid, int flags, const struct itimerspec *new_value, struct itimerspec *old_value);

/*
 * Poll given timer timerid. Return the residual time in curr_value.
 * - If timer is not set, cur_value fields are set to 0
 * - If timer is set, curr_value->it_value are set according to clockid
 * - If timer is set and is periodic, the timer period is also added to curr_value->it_interval
 */
int timer_gettime(timer_t timerid, struct itimerspec *curr_value);

/*
 * Get current time for clock identifier clockid in timespec sp (POSIX API)
 */
int clock_gettime(clockid_t clockid, struct timespec *tp);

#endif

#endif/*TIME_H_*/
