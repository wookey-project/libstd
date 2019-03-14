#ifndef PRINT_H
#define PRINT_H

#include <stdarg.h>
#include "api/types.h"


void printf(char *fmt, ...);

void aprintf(char *fmt, ...);

void aprintf_flush(void);

uint32_t sprintf(char *dst, uint16_t len, char *fmt, ...);

/* others, non-POSIX compliant */

void hexdump(const uint8_t *bin, uint32_t len);

void      itoa(uint64_t        value,
               uint8_t         base);



#endif
