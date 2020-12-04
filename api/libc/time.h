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
 */

int timer_create(clockid_t clockid, struct sigevent *sevp, timer_t *timerid);

int timer_settime(timer_t timerid, int flags, const struct itimerspec *new_value, struct itimerspec *old_value);

int timer_gettime(timer_t timerid, struct itimerspec *curr_value);

#endif

#endif/*TIME_H_*/
