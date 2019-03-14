#ifndef NOSTD_H_
#define NOSTD_H_

#include "api/types.h"

void itoa(uint64_t value, uint8_t base);

void hexdump(const uint8_t *bin, uint32_t len);

#endif/*!NOSTD_H_*/
