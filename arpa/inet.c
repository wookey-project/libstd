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
#include "api/regutils.h"

#include "api/arpa/inet.h"

static inline uint32_t to_big32(uint32_t value)
{
    return ((value & 0xff) << 24) | ((value & 0xff00) << 8)
        | ((value & 0xff0000) >> 8) | ((value & 0xff000000) >> 24);
}

static inline uint16_t to_big16(uint16_t value)
{
    return ((value & 0xff) << 8) | ((value & 0xff00) >> 8);
}

static inline uint32_t to_little32(uint32_t value)
{
    return ((value & 0xff) << 24) | ((value & 0xff00) << 8)
        | ((value & 0xff0000) >> 8) | ((value & 0xff000000) >> 24);
}

static inline uint16_t to_little16(uint16_t value)
{
    return ((value & 0xff) << 8) | ((value & 0xff00) >> 8);
}

/*
 * \brief host (variable) to network (MSB) byte order conversion for short integer
 *
 * \param hostshort the value to convert
 *
 * \return the MSB encoded value
 *
 * Conforming to:
 *   POSIX.1-2001, POSIX.1-2008
 */
uint16_t htons(uint16_t hostshort)
{
    uint16_t netshort = hostshort;
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    netshort = to_big16(hostshort);
#endif
    return netshort;
}

/*
 * \brief host (variable) to network (MSB) byte order conversion for long integer
 *
 * \param hostlong the value to convert
 *
 * \return the MSB encoded value
 *
 * Conforming to:
 *   POSIX.1-2001, POSIX.1-2008
 */
uint32_t htonl(uint32_t hostlong)
{
    uint32_t netlong = hostlong;
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    netlong = to_big32(hostlong);
#endif
    return netlong;
}

/*
 * \brief network (MSB) to host (variable) byte order conversion for short integer
 *
 * \param netshort the value to convert
 *
 * \return the host byte order encoded value
 *
 * Conforming to:
 *   POSIX.1-2001, POSIX.1-2008
 */
uint16_t ntohs(uint16_t netshort)
{
    uint16_t hostshort = netshort;
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    hostshort = to_little16(netshort);
#endif
    return hostshort;
}

/*
 * \brief network (MSB) to host (variable) byte order conversion for long integer
 *
 * \param netlong the value to convert
 *
 * \return the MSB ordered value
 *
 * Conforming to:
 *   POSIX.1-2001, POSIX.1-2008
 */
uint32_t ntohl(uint32_t netlong)
{
    uint32_t hostlong = netlong;
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    hostlong = to_little32(netlong);
#endif
    return hostlong;
}
