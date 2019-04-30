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
#include "libc/stdio.h"
#include "libc/stdarg.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/types.h"
#include "libc/syscall.h"
#include "string/string_priv.h"

static int _hexdump(const uint8_t * bin, uint8_t len)
{
    /* NOTE: since our unerlying printf/log system call 
     * adds a line break at each call, we have to first
     * push the input of hexdump in a local buffer.
     * For stack size reasons, we limit the input buffer to 255 bytes,
     * hence limiting our local buffer length to (255*3)+1 bytes.
     */
    /* 3 chars per byte, plus the terminating '\0' char */
    char    buf[(255 * 3) + 1];
    int     res = 0;

    for (uint32_t i = 0; i < len; i++) {
        /* each hexadecimal value is printed using two hex char, padding
         * with zero if needed. making the string having a fixed size */
        sprintf(&(buf[i * 3]), "%02x ", bin[i]);
    }
    res = printf("%s\n", buf);
    return res;
}


int hexdump(const uint8_t * bin, int len)
{
    int     res, consumed, to_print;

    if (len <= 0) {
        return 0;
    }
    consumed = 0;
    while (consumed <= len) {
        to_print = ((len - consumed) < 255) ? (len - consumed) : 255;
        /* Sanity check for overflow */
        if (consumed > len) {
            goto end;
        }
        res += _hexdump(bin + consumed, to_print);
        consumed += to_print;
    }
 end:
    return res;
}
