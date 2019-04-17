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
#ifndef H_MALLOC
#define H_MALLOC

#include "autoconf.h"
#include "libc/types.h"

#ifdef CONFIG_STD_MALLOC


/********************************************************************************/

/* Block security options (values for flag) */

#define ALLOC_NORMAL        (int) 0x00000000
#define ALLOC_SENSITIVE     (int) 0xFFFFFFFF


/* Function prototypes */

int wmalloc_init(void);

#if CONFIG_STD_MALLOC_SIZE_LEN == 16
int wmalloc(void **ptr_to_alloc, const uint16_t len, const int flag);
#elif CONFIG_STD_MALLOC_SIZE_LEN == 32
int wmalloc(void **ptr_to_alloc, const uint32_t len, const int flag);
#endif

int wfree(void **ptr_to_free);


#endif

#endif

