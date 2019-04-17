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
#ifndef STDIO_H_
#define STDIO_H_

#include "libc/stdarg.h"
#include "libc/types.h"

/*******************************************
 * Implementation of POSIX stdio
 *******************************************/


/****************************************
 * printf() familly
 *
 * This implementation of printf implement a subset
 * of the POSIX.1-2001 and C99 standard API (as we are in an embedded system)
 * Although, the behavior of the functions for the supported flags chars
 * and lenght modifiers is conform to the standard.
 *
 * The following is supported:
 *
 * flag characters:
 *
 * '0'   the value should be zero-padded. This flag is allowed for any
 *       numerical value, including pointer (p).
 *       This flag *must* be followed by a numerical, decimal value specifying
 *       the size to which the value must be padded.
 *
 *  length modifier:
 *
 *  'l'      long int conversion
 *  'll'     long long int conversion
 *  'd','i'  integer signed value conversion
 *  'u'      unsigned integer value conversion
 *  'h'      short int conversion
 *  'hh'     unsigned char conversion
 *  'x'      hexadecimal value, mapped on a long integer conversion
 *  'o'      octal value, mapped on a long integer conversion
 *  'p'      pointer, word-sized unsigned integer, starting with 0x and padded
 *           with 0 up to word-length size
 *  'c'      character value conversion
 *  's'      string conversion
 *
 *  other flags characters and length modifiers are not supported,
 *  generating an immediate stop of the fmt parsing.
 *
 * Conforming (for the supported flags and length modifier and error return)
 * to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99
 *
 */

/*
 * \brief formatted printing to the standard console.
 *
 * Printing is synchronous, including a syscall execution.
 *
 * \param fmt the formated string to print
 * \return the number of characters printed on success, -1 on failure
 */
int printf(const char *fmt, ...);

/*
 * formatted printing to a given buffer, printing at most len chars,
 * including the terminating character into dst.
 */
int snprintf(char *dst, size_t len, const char *fmt, ...);

/*
 * formatted printing to a given buffer.
 */
int sprintf(char *dst, const char *fmt, ...);

/****************************************
 * stdargs vprintf() familly
 *
 * This implementation of printf implement a subset
 * of the POSIX.1-2001 and C99 standard API (as we are in an embedded system)
 * Although, the behavior of the functions for the supported flags chars
 * and lenght modifiers is conform to the standard.
 *
 * The following is supported:
 *
 * flag characters:
 *
 * '0'   the value should be zero-padded. This flag is allowed for any
 *       numerical value, including pointer (p).
 *       This flag *must* be followed by a numerical, decimal value specifying
 *       the size to which the value must be padded.
 *
 *  length modifier:
 *
 *  'l'      long int conversion
 *  'll'     long long int conversion
 *  'd','i'  integer signed value conversion
 *  'u'      unsigned integer value conversion
 *  'h'      short int conversion
 *  'hh'     unsigned char conversion
 *  'x'      hexadecimal value, mapped on a long integer conversion
 *  'o'      octal value, mapped on a long integer conversion
 *  'p'      pointer, word-sized unsigned integer, starting with 0x and padded
 *           with 0 up to word-length size
 *  'c'      character value conversion
 *  's'      string conversion
 *
 *  other flags characters and length modifiers are not supported,
 *  generating an immediate stop of the fmt parsing.
 *
 * Conforming (for the supported flags and length modifier and error return)
 * to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99
 *
 */

/*
 * \brief formatted printing to the standard console using va_list.
 *
 * Printing is synchronous, including a syscall execution.
 *
 * \param fmt the formated string to print
 * \return the number of characters printed on success, -1 on failure
 */
int vprintf(const char *fmt, va_list args);

/*
 * formatted printing to a given buffer, printing at most len chars, using va_list,
 * including the terminating character into dst.
 */
int vsnprintf(char *dst, size_t len, const char *fmt, va_list args);

/*
 * formatted printing to a given buffer, using va_list.
 */
int vsprintf(char *dst, const char *fmt, va_list args);



#endif/*!STDIO_H_*/
