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
#ifndef SYS_TYPES_H_
#define SYS_TYPES_H_
/* this is a (part of) POSIX sys/types.h standard header for embedded needs */

#include "autoconf.h"

#ifdef CONFIG_ARCH_ARMV7M
# include "libc/arch/cores/armv7-m/types.h"
#else
# error "architecture not yet supported"
#endif

typedef __ssize_t ssize_t;
typedef __size_t size_t;

#endif/*SYS_TYPES_H_*/
