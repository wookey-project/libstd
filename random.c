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
#include "api/types.h"
#include "api/stdio.h"
#include "api/nostd.h"
#include "api/string.h"
#include "api/syscall.h"
#include "api/random.h"

int get_random(unsigned char *buf, uint16_t len)
{
    uint16_t i;
    uint8_t ret;

    /* First, set the buffer to zero */
    memset(buf, 0, len);

    /* Generate as much random as necessary */
    for(i = 0; i < sizeof(uint32_t) * (len / sizeof(uint32_t)); i += sizeof(uint32_t)){
        if((ret = sys_get_random((char*)(&(buf[i])), 4))){
            printf("error while getting random ! ret=%d\n", ret);
            goto err;
        }
    }
    if((len - i) > (int16_t)sizeof(uint32_t)){
        /* We should not end here ... */
        goto err;
    }
    /* Handle the remaining bytes */
    if(i < len){
        uint32_t random;
        if((ret = sys_get_random(((char*)&random), 4))){
            printf("error while getting random ! ret=%d\n", ret);
            goto err;
        }
        while(i < len){
            buf[i] = (random >> (8 * (len - i))) & 0xff;
            i++;
        }
    }

    return 0;
err:
    return -1;
}
