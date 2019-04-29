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
#ifndef NOSTD_H_
#define NOSTD_H_

#include "libc/types.h"

/**
 * \brief Dumping hexadecimal value from a given buffer bin of length len.
 *
 * \param bin the input binary content
 * \param len the length (in bytes) of the binary content
 *
 * \return the number of printed characters (should be bigger than the
 *         input buffer len
 *
 *
 * INFO: has the hexdump is a one line printing content, dumping a
 * buffer using successive hexdump() call is performed.
 */
int hexdump(const uint8_t *bin, int len);

/*
 * This is an asyncrhonous implementation of the POSIX printf API.
 * This imlementation support, like the stdio printf(), a subset
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
 * As the implementation is asyncrhonous, the generated string is keeped in
 * the local ring buffer, making the aprintf() function eligible in ISR
 * execution.
 *
 * WARNING: the userspace implementation is responsible for regulary flushging
 * the ring buffer using the aprintf_flush() API in the main thread execution
 * context.
 */

/*
 * asynchronous printf implementation
 */
int aprintf(const char *fmt, ...);

/*
 * flushing the ring buffer content that pervious asyncrhonous printf may
 * have fullfilled.
 */
int aprintf_flush(void);

#endif/*!NOSTD_H_*/
