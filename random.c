/* Top header for AES */
#include "api/types.h"
#include "api/print.h"
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
