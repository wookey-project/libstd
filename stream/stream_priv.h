#ifndef STREAM_PRIV_H_
# define STREAM_PRIV_H_

#include <stdarg.h>
#include "api/types.h"

#define BUF_SIZE	512
#define BUF_MAX		(BUF_SIZE - 1)

struct s_ring {
    uint32_t start;
    uint32_t end;
    bool     full;
    char buf[BUF_SIZE];
};

void init_ring_buffer(void);

void print_and_reset_buffer(void);

int print(char *fmt, va_list args);

#endif/*!STREAM_PRIV_H_*/
