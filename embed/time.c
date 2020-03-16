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
#include "libc/types.h"
#include "libc/time.h"
#include "autoconf.h"
#include "libc/syscall.h"

/*
 * Active wait, *not* POSIX compliant
 */
void waitfor(uint32_t ms)
{
    uint64_t val;
    uint64_t val2;
    sys_get_systick(&val, PREC_MILLI);
    do {
        sys_get_systick(&val2, PREC_MILLI);
    } while ((val2 - val) < ms);
}

unsigned int sleep(unsigned int second)
{
    unsigned int val = 0;
    int ret;
    struct timespec req = {
        .tv_sec = second,
        .tv_nsec = 0
    };
    struct timespec rem = {
        .tv_sec = 0,
        .tv_nsec = 0
    };
    ret = nanosleep(&req, &rem);
    if (ret == -1) {
        val = rem.tv_sec;
    }
    return val;
}

/*
 * TODO: missing errno handling, idealy thread-safe errno handling (per-thread errno)...
 */
int nanosleep(const struct timespec *req, struct timespec *rem)
{
    int ret = 0;
    uint32_t msec;
    uint64_t val;
    uint64_t val_end;
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitation */
    if (!req || !rem) {
        errcode = MBED_ERROR_INVPARAM;
        ret = -1;
        goto end;
    }
    /* POSIX conformance */
    if (req->tv_nsec == 0 && req->tv_sec ==0) {
        /* just... don't wait */
        goto end;
    }
    if (req->tv_nsec < 0 || req->tv_nsec > 999999999) {
        errcode = MBED_ERROR_INVPARAM;
        ret = -1;
        goto end;
    }

    /* get back time from nsec, fallbacking to sec */
    if (req->tv_nsec != 0) {
        /* nsec in miliseconds, rounded to upper value */
        msec = (uint32_t)req->tv_nsec / 1000000;
        if (msec == 0) {
            msec = 1;
        }
    } else {
        if (req->tv_sec > 4*1024*1024) {
            /* overflow when converting to msec... refusing to wait */
            errcode = MBED_ERROR_INVPARAM;
            ret = -1;
            goto end;
        }
        msec = (uint32_t)req->tv_sec * 1000;
    }
    /* after conformance, we can encode the nsec in uint32_t variable */
    sys_get_systick(&val, PREC_MILLI);
    sys_sleep(msec, SLEEP_MODE_INTERRUPTIBLE);
    sys_get_systick(&val_end, PREC_MILLI);
    /* here we check if we have been awoken before the end of calculated sleep,
     * with a 1ms imprecision due to successive systick calculation.
     * TODO: this is not clean and should be replaced by a dedicated return
     *       value of sys_sleep, specifying if an interrupt awoken the task */
    if ((val_end - val) < (msec - 1)) {
        errcode = MBED_ERROR_INTR;
        rem->tv_nsec = (msec - (val_end - val)) * 1000 * 1000;
        rem->tv_sec = (msec - (val_end - val)) / 1000;
        ret = -1;
        goto end;
    }
end:
    return ret;
}
