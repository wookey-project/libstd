#ifndef STD_PRINT_PRIV_
#define STD_PRINT_PRIV_

#include "api/print.h"
/*
 * private stuff for libstd itself
 */

#define BUF_SIZE	512
#define BUF_MAX		(BUF_SIZE - 1)

struct s_ring {
    uint32_t start;
    uint32_t end;
    char buf[BUF_SIZE];
}; 

void print(char *fmt, va_list args);

void init_ring_buffer(void);

struct s_ring *stream_rb_get(void);

#endif                          /*!STD_PRINT_PRIV_ */
