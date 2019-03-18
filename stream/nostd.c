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
#include "api/stdio.h"
#include "api/nostd.h"
#include "api/string.h"
#include "api/types.h"
#include "api/syscall.h"
#include "stream/stream_priv.h"
#include "string/string_priv.h"

int hexdump(const uint8_t *bin, uint32_t len)
{
    /* 3 chars per byte, plus the terminating char */
    uint16_t buflen = len*3+1;
    char buf[buflen];
    int res = 0;

    for (uint32_t i = 0; i < len; i++) {
        /* each hexadecimal value is printed using two hex char, padding
         * with zero if needed. making the string having a fixed size */
        sprintf(&(buf[i*3]), "%02x ", bin[i]);
    }
    res = printf("%s\n", buf);
    return res;
}

