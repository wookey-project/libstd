#ifndef STRING_H
#define STRING_H

/*!
 * \file string oriented manipulation functions
 */

#include "api/types.h"

uint32_t strlen(const char *s);

char *strncpy(char *dest, const char *src, uint32_t n);

void itoa(unsigned long long value, uint8_t base);

uint32_t sprintf(char *dst, uint16_t len, char *fmt, ...);

int      strcmp(const char *s1, const char *s2);

#endif
