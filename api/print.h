#ifndef PRINT_H
#define PRINT_H

#include <stdarg.h>
#include "api/types.h"

void *memcpy(void *dest, const void *src, uint32_t n);

void printf(char *fmt, ...);

uint32_t sprintf(char *dst, uint16_t len, char *fmt, ...);

uint32_t strlen(const char *s);

char *strncpy(char *dest, const char *src, uint32_t n);

const char *strerror(uint8_t ret);

void *memset(void *s, int c, uint32_t n);

int memcmp(const void *s1, const void *s2, int n);

void hexdump(const uint8_t *bin, uint32_t len);

void itoa(unsigned long long value, uint8_t base);

#endif
