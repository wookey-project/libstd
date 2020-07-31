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
#ifndef REGUTILS_H_
#define REGUTILS_H_
#include "libc/types.h"

#define REG_ADDR(addr)                      ((register_t)(addr))
#define REG_VALUE(reg, value, pos, mask)    ((reg)  |= (((value) << (pos)) & (mask)))

#define SET_BIT(REG, BIT)     ((REG) |= (BIT))
#define CLEAR_BIT(REG, BIT)   ((REG) &= ~(BIT))
#define READ_BIT(REG, BIT)    ((REG) & (BIT))
#define CLEAR_REG(REG)        ((REG) = (0x0))

#define ARRAY_SIZE(array, type)	(sizeof(array) / sizeof(type))

/* implicit convertion to int */
#define MIN(x, y) (((x) < (y)) ? (x) : (y))

__INLINE uint8_t min_u8(uint8_t x, uint8_t y)
{
    if (x < y)
        return x;
    else
        return y;
}

/*
 * These macros assume that the coding style (bits_name_Msk and bits_name_Pos)
 * is respected when defining registers bitfields
 */
#define set_reg(REG, VALUE, BITS)	set_reg_value(REG, VALUE, BITS##_Msk, BITS##_Pos)
#define get_reg(REG, BITS)		get_reg_value(REG, BITS##_Msk, BITS##_Pos)

__INLINE uint32_t get_reg_value(volatile const uint32_t * reg, uint32_t mask,
                                uint8_t pos);
__INLINE int8_t set_reg_value(register_t reg, uint32_t value,
                              uint32_t mask, uint8_t pos);

__INLINE uint32_t read_reg_value(register_t reg);
__INLINE uint16_t read_reg16_value(volatile uint16_t * reg);
__INLINE void write_reg_value(register_t reg, uint32_t value);
__INLINE void write_reg16_value(volatile uint16_t * reg, uint16_t value);

__INLINE void set_reg_bits(register_t reg, uint32_t value);
__INLINE void clear_reg_bits(register_t reg, uint32_t value);

__INLINE uint32_t get_reg_value(volatile const uint32_t * reg, uint32_t mask,
                                uint8_t pos)
{
    if ((mask == 0x00) || (pos > 31))
        return 0;

    return (uint32_t) (((*reg) & mask) >> pos);
}

__INLINE uint16_t get_reg16_value(volatile uint16_t * reg, uint16_t mask,
                                  uint8_t pos)
{
    if ((mask == 0x00) || (pos > 15))
        return 0;

    return (uint16_t) (((*reg) & mask) >> pos);
}

__INLINE int8_t set_reg_value(register_t reg, uint32_t value,
                              uint32_t mask, uint8_t pos)
{
    uint32_t tmp;

    if (pos > 31)
        return -1;

    if (mask == 0xFFFFFFFF) {
        (*reg) = value;
    } else {
        tmp = read_reg_value(reg);
        tmp &= ~mask;
        tmp |= (value << pos) & mask;
        write_reg_value(reg, tmp);
    }

    return 0;
}

__INLINE int8_t set_reg16_value(volatile uint16_t * reg, uint16_t value,
                                uint16_t mask, uint8_t pos)
{
    uint16_t tmp;

    if (pos > 15)
        return -1;

    if (mask == 0xFFFF) {
        (*reg) = value;
    } else {
        tmp = read_reg16_value(reg);
        tmp &= (uint16_t) ~ mask;
        tmp |= (uint16_t) ((value << pos) & mask);
        write_reg16_value(reg, tmp);
    }

    return 0;
}

__INLINE uint32_t read_reg_value(register_t reg)
{
    return (uint32_t) (*reg);
}

__INLINE uint16_t read_reg16_value(volatile uint16_t * reg)
{
    return (uint16_t) (*reg);
}

__INLINE void write_reg_value(register_t reg, uint32_t value)
{
    (*reg) = value;
}

__INLINE void write_reg16_value(volatile uint16_t * reg, uint16_t value)
{
    (*reg) = value;
}

__INLINE void set_reg_bits(register_t reg, uint32_t value)
{
    *reg |= value;
}

__INLINE void set_reg16_bits(volatile uint16_t * reg, uint16_t value)
{
    *reg |= value;
}

__INLINE void clear_reg_bits(register_t reg, uint32_t value)
{
    *reg &= (uint32_t) ~ (value);
}

#endif                          /*!REGUTILS_H_ */
