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
#ifndef SEMAPHORE_H_
#define SEMAPHORE_H_

/* semaphore, with potential concurrent access allowed */
void semaphore_init(uint8_t value, volatile uint32_t* semaphore);

bool semaphore_trylock(volatile uint32_t* semaphore);

void semaphore_lock(volatile uint32_t* semaphore);

bool semaphore_release(volatile uint32_t* semaphore);

/* effective mutex (Mutual Exclusion) */
void mutex_init(volatile uint32_t* mutex);

bool mutex_trylock(volatile uint32_t* mutex);

void mutex_lock(volatile uint32_t* mutex);

void mutex_unlock(volatile uint32_t* mutex);

bool mutex_tryunlock(volatile uint32_t* mutex);

#endif
