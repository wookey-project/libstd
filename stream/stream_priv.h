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
#ifndef STREAM_PRIV_H_
# define STREAM_PRIV_H_

#include <stdarg.h>
#include "libc/types.h"

#define BUF_MAX	512

struct s_ring {
    uint32_t start;
    uint32_t end;
    bool     full;
    char buf[BUF_MAX];
};

void init_ring_buffer(void);

void print_and_reset_buffer(void);

int print(const char *fmt, va_list args);

#endif/*!STREAM_PRIV_H_*/
