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
