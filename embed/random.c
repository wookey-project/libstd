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
/* Top header for AES */
#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/syscall.h"
#include "libc/random.h"

mbed_error_t get_random(unsigned char *buf, uint16_t len)
{
    uint16_t i;
    uint8_t ret;
    mbed_error_t err = MBED_ERROR_NONE;

    /*sanitize */
    if (!buf) {
        err = MBED_ERROR_INVPARAM;
        goto error;
    }

    /* First, set the buffer to zero */
    memset(buf, 0, len);

    /* Generate as much random as necessary */
    for(i = 0; i < sizeof(uint32_t) * (len / sizeof(uint32_t)); i += sizeof(uint32_t)) {
        if((ret = sys_get_random((char*)(&(buf[i])), 4))) {
            if (ret == SYS_E_DENIED) {
                err = MBED_ERROR_DENIED;
            } else if (ret == SYS_E_BUSY) {
                err = MBED_ERROR_BUSY;
            } else {
                err = MBED_ERROR_UNKNOWN;
            }
            goto error;
        }
    }
    if((len - i) > (int16_t)sizeof(uint32_t)) {
        /* We should not end here, the buf len is not 32 bits multiple */
        err = MBED_ERROR_INVPARAM;
        goto error;
    }
    /* Handle the remaining bytes */
    if(i < len){
        uint32_t random;
        if((ret = sys_get_random(((char*)&random), 4))) {
            if (ret == SYS_E_DENIED) {
                err = MBED_ERROR_DENIED;
            } else if (ret == SYS_E_BUSY) {
                err = MBED_ERROR_BUSY;
            } else {
                err = MBED_ERROR_UNKNOWN;
            }
            goto error;
        }
        while(i < len){
            buf[i] = (random >> (8 * (len - i))) & 0xff;
            i++;
        }
    }
error:
    return err;
}
