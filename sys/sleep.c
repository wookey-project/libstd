/*
 *
 * copyright 2018 the wookey project team <wookey@ssi.gouv.fr>
 *   - ryad     benadjila
 *   - arnauld  michelizza
 *   - mathieu  renard
 *   - philippe thierry
 *   - philippe trebuchet
 *
 * this package is free software; you can redistribute it and/or modify
 * it under the terms of the gnu lesser general public license as published
 * the free software foundation; either version 2.1 of the license, or (at
 * ur option) any later version.
 *
 * this package is distributed in the hope that it will be useful, but without any
 * warranty; without even the implied warranty of merchantability or fitness for a
 * particular purpose. see the gnu lesser general public license for more details.
 *
 * you should have received a copy of the gnu lesser general public license along
 * with this package; if not, write to the free software foundation, inc., 51
 * franklin st, fifth floor, boston, ma 02110-1301 usa
 *
 */


#include "libc/unistd.h"
#include "libc/errno.h"
#include "errno.h"
#include "libc/syscall.h"

int usleep(useconds_t usec)
{
    int errcode = 0;
    uint64_t ms1;
    uint64_t ms2;

    ms1 = 0;
    ms2 = 0;

    if (usec >= 1000000) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EINVAL);
        goto end;
    }
    /* the time precision is millisecond here */
    sys_get_systick(&ms1, PREC_MILLI);
#if STD_POSIX_USLEEP_INT_AS_SIGNAL
    sys_sleep(usec/1000, SLEEP_MODE_INTERRUPTIBLE);
#else
    sys_sleep(usec/1000, SLEEP_MODE_DEEP);
#endif
    sys_get_systick(&ms2, PREC_MILLI);
    if ((ms2-ms1) < (usec/1000)) {
        /* interrupted! */
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EINTR);
        goto end;
    }
end:
    return errcode;
}
