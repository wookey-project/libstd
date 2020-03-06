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
#include "libc/types.h"

/*
 * INFO: these two functions are generic abstraction to memory low level
 * handling. On MPU based systems, these functions do nearly nothing.
 * On MMU based system, these functions really execution a memory mapping
 * request when needed.
 * The call is to keep a unified, portable, abstraction of the memory
 * handling mechanism for the allocator (malloc()/free() implementation),
 */

/*
 * request for memory space mapping.
 * On MPU based system, this function just check that the (non-null) requested
 * address of length size is in the task memory region. If it is, mmap return
 * addr. If not, it returns NULL.
 * on MPU based system, prot and flags are not handled. These flags are
 * handled in MMU based systems.
 */
void *mmap(void *addr, size_t length, int prot, int flags,
           int fd, off_t offset);

/*
 * munmap just do nothing in MPU based systems. It returns 0 if the memory
 * block to free is in the task data memory region, or -1 if it is not.
 */
int munmap(void *addr, size_t length);

