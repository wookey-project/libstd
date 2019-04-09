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
#ifndef TYPES_H_
#define TYPES_H_

#include "autoconf.h"

#ifdef CONFIG_ARCH_ARMV7M
# include "arch/cores/armv7-m/types.h"
#else
# error "architecture not yet supported"
#endif

typedef enum {false = 0, true = 1} bool;
/* Secure boolean against fault injections for critical tests */
typedef enum {secfalse = 0x55aa55aa, sectrue = 0xaa55aa55} secbool;

#if defined(__CC_ARM)
# define __ASM            __asm  /* asm keyword for ARM Compiler    */
# define __INLINE         static __inline    /* inline keyword for ARM Compiler */
# define __UNUSED                /* [PTH] todo: find the way to set a function/var unused */
#elif defined(__GNUC__)
# define __ASM            __asm  /* asm keyword for GNU Compiler    */
# define __INLINE        static inline
# define __UNUSED        __attribute__((unused))
# define __packed		__attribute__((__packed__))
#endif

#define __in            /* indication for function arguments (Ada like) */
#define __out           /* indication for function arguments (Ada like) */
#define __inout         /* indication for function arguments (Ada like) */

/*
 * This enumerate defines a list of usual errors that arrise in embedded systems, that can
 * be used in all drivers, stacks, libs and application as a unified error handling mechanism
 * Each stack can translate these errors into stack-specific error to the host depending on
 * the protocol standard (SDIO, SCSI, DFU...)
 */
typedef enum {
    MBED_ERROR_NONE = 0,
    MBED_ERROR_NOMEM,
    MBED_ERROR_NOSTORAGE,
    MBED_ERROR_NOBACKEND,
    MBED_ERROR_INVCREDENCIALS,
    MBED_ERROR_UNSUPORTED_CMD,
    MBED_ERROR_INVSTATE,
    MBED_ERROR_NOTREADY,
    MBED_ERROR_BUSY,
    MBED_ERROR_DENIED,
    MBED_ERROR_UNKNOWN,
    MBED_ERROR_INVPARAM,
    MBED_ERROR_WRERROR,
    MBED_ERROR_RDERROR,
    MBED_ERROR_INITFAIL
} mbed_error_t;

#endif/*!TYPES_H_*/
