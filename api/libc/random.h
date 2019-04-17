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
#ifndef RANDOM_H_
#define RANDOM_H_

#include "libc/types.h"

/**
 * \fn get_random
 * \brief load random content from the system entropy source into a buffer
 *
 * \param buf  the buffer in which the random values is to be stored
 * \param len  the amount of random bytes requested
 *
 * \return MBED_ERROR_NONE if the RNG source fullfill the buffer, or:
 *    MBED_ERROR_DENIED if the task is not authorized to request RNG source
 *    MBED_ERROR_BUSY if the RNG source entropy is not ready
 *    MBED_ERROR_INVPARAM if len is not 32bit aligned or the buffer is NULL.
 *
 */
mbed_error_t  get_random(unsigned char *buf, uint16_t len);

#endif
