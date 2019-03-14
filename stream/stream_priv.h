#ifndef STREAM_PRIV_H_
# define STREAM_PRIV_H_

#include "api/types.h"

#define BUF_SIZE	512
#define BUF_MAX		(BUF_SIZE - 1)

struct s_ring {
    uint32_t start;
    uint32_t end;
    bool     full;
    char buf[BUF_SIZE];
};

void write_digit(uint8_t digit);

void copy_string(char *str, uint32_t len);

void print_and_reset_buffer(void);

void init_ring_buffer(void);

#endif/*!STREAM_PRIV_H_*/
