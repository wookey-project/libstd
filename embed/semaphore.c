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
#include "api/types.h"
#include "autoconf.h"
#ifdef CONFIG_ARCH_ARMV7M
#include "arch/cores/armv7-m/m4-sync.h"
#else
#error "Unknown architecture"
#endif
#include "semaphore.h"

/*
 * The semaphore is initialized with 'value'.
 * value determine the number of concurrent threads that can access
 * a ressource in the same time.
 * If value is 1, this semaphore is a mutex
 */
void semaphore_init(uint8_t value, volatile uint32_t *semaphore)
{
    *semaphore = value;
}

/*
 * Try to lock the current semaphore
 */
bool semaphore_trylock(volatile uint32_t* semaphore)
{
    return core_semaphore_trylock(semaphore);
}

void semaphore_lock(volatile uint32_t* semaphore)
{
    bool is_locked = false;
    do {
        is_locked = core_semaphore_trylock(semaphore);
    } while (!is_locked);
}



bool semaphore_release(volatile uint32_t* semaphore)
{
    return core_semaphore_release(semaphore);
}
