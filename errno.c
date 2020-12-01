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
#include "autoconf.h"
#include "libc/types.h"
#include "libc/errno.h"
#include "libc/sync.h"
#ifdef CONFIG_ARCH_ARMV7M
#include "arch/cores/armv7-m/m4_syscall.h"
#else
#error "Architecture not yet supported by Libstd Syscall API"
#endif



/*
 * TODO: for future multithreads support, this value should be Kconfig-based
 */
#define MAX_CTX_PER_TASK 2

/*
 * This is the local ISO C, thread-safe, errno implementation.
 *
 * As we use a microkernel implementation, most of the errno set (for POSIX compatibility)
 * is made by the libstd itslef. Yet, errno access from out of the libstd **must** be keeped
 * const (errno is a read-only variable for most of the userspace code).
 */
static int errno_v[MAX_CTX_PER_TASK];

int __errno_location(void) {
    uint8_t ctx = get_current_ctx_id();
    return errno_v[ctx];
}

mbed_error_t __libstd_set_errno(int val) {
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (val < EPERM || val > ERANGE) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    errno_v[get_current_ctx_id()] = val;
    request_data_membarrier();
err:
    return errcode;
}
