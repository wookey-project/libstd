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
#include "libc/sys/types.h"

#define KBYTE 1024
#define MBYTE 1048576
#define GBYTE 1073741824

typedef enum {false = 0, true = 1} bool;
/* Secure boolean against fault injections for critical tests */
typedef enum {secfalse = 0x55aa55aa, sectrue = 0xaa55aa55} secbool;

#if defined(__CC_ARM)
# define __ASM            __asm  /* asm keyword for ARM Compiler    */
# define __INLINE         static __inline    /* inline keyword for ARM Compiler */
# define __UNUSED                /* [PTH] todo: find the way to set a function/var unused */

/* support for compilers that don't support expect builtin */
# define likely(x)  x
# define unlikely(x) x
# define likely_value(x,val) x


#elif defined(__GNUC__)
# define __ASM            __asm  /* asm keyword for GNU Compiler    */
# define __INLINE        static inline
# define __UNUSED        __attribute__((unused))
# define __packed		__attribute__((__packed__))

/*
 * boolean Likely for if() branch prediction. Compatible with GCC & LLVM
 *
 * e.g.
 * if (likely(boolean_expression)) {
 * }
 */
#define likely(x)      __builtin_expect(!!(x), 1)
#define unlikely(x)    __builtin_expect(!!(x), 0)

/*
 * for switch/case
 * e.g.
 * switch(likely_value(x,5)) {
 *    case 1:
 *      ...
 *    case 5:
 *      ... // the likely one
 */
#define likely_value(x,val) __builtin_expect(x,val)


#endif

#define __in            /* indication for function arguments (Ada like) */
#define __out           /* indication for function arguments (Ada like) */
#define __inout         /* indication for function arguments (Ada like) */

#if defined(__GNUC__) && __GNUC__ > 6
#define __explicit_fallthrough __attribute__ ((fallthrough));
#else
#define __explicit_fallthrough
#endif


/*
 * This enumerate defines a list of usual errors that arrise in embedded systems, that can
 * be used in all drivers, stacks, libs and application as a unified error handling mechanism
 * Each stack can translate these errors into stack-specific error to the host depending on
 * the protocol standard (SDIO, SCSI, DFU...)
 */
typedef enum {
    MBED_ERROR_NONE              = 0,
    MBED_ERROR_NOMEM             = 1,
    MBED_ERROR_NOSTORAGE         = 2,
    MBED_ERROR_NOBACKEND         = 3,
    MBED_ERROR_INVCREDENCIALS    = 4,
    MBED_ERROR_UNSUPORTED_CMD    = 5,
    MBED_ERROR_INVSTATE          = 6,
    MBED_ERROR_NOTREADY          = 7,
    MBED_ERROR_BUSY              = 8,
    MBED_ERROR_DENIED            = 9,
    MBED_ERROR_UNKNOWN           = 10,
    MBED_ERROR_INVPARAM          = 11,
    MBED_ERROR_WRERROR           = 12,
    MBED_ERROR_RDERROR           = 13,
    MBED_ERROR_INITFAIL          = 14,
    MBED_ERROR_TOOBIG            = 15,
    MBED_ERROR_NOTFOUND          = 16,
    MBED_ERROR_INTR              = 16,
} mbed_error_t;

#ifdef __FRAMAC__
/*@ predicate is_valid_error(mbed_error_t i) =
    i == MBED_ERROR_NONE ||
    i == MBED_ERROR_NOMEM ||
    i == MBED_ERROR_NOSTORAGE ||
    i == MBED_ERROR_NOBACKEND ||
    i == MBED_ERROR_INVCREDENCIALS ||
    i == MBED_ERROR_UNSUPORTED_CMD ||
    i == MBED_ERROR_INVSTATE ||
    i == MBED_ERROR_NOTREADY ||
    i == MBED_ERROR_BUSY ||
    i == MBED_ERROR_DENIED ||
    i == MBED_ERROR_UNKNOWN ||
    i == MBED_ERROR_INVPARAM ||
    i == MBED_ERROR_WRERROR ||
    i == MBED_ERROR_RDERROR ||
    i == MBED_ERROR_INITFAIL ||
    i == MBED_ERROR_TOOBIG ||
    i == MBED_ERROR_NOTFOUND ||
    i == MBED_ERROR_INTR;
*/
#endif


#endif/*!TYPES_H_*/
