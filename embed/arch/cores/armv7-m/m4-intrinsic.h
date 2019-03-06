#ifndef M4_INTRINSIC
#define M4_INTRINSIC

#include "types.h"

/*
 * intrinsic functions of CMSIS, not implemented in GCC, are implemented here,
 * as ASM code
 */
void     __BPKT(void);

void     __DSB(void);
void     __DMB(void);
void     __ISB(void);

uint32_t __STREXW(uint32_t val, volatile uint32_t *addr);
uint32_t __STREXH(uint16_t val, volatile uint32_t *addr);
uint32_t __STREXB(uint8_t  val, volatile uint32_t *addr);

#endif/*!M4_INTRINSIC*/
