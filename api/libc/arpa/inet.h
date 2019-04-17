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
#ifndef ARPA_INET_H_
#define ARPA_INET_H_

/*
 * This is a basic implementation of the arpa/inet.h API.
 *
 * This API includes the POSIX conforment byteorder manipulation, which
 * can be used for network communication and any other byte-ordered protocol
 * (such as SCSI).
 *
 * INFO: non standard POSIX compliant API such as htobe/htole... are not implemented
 *
 */

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
uint16_t htons(uint16_t hostshort);

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
uint32_t htonl(uint32_t hostlong);

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
uint16_t ntohs(uint16_t netshort);

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
uint32_t ntohl(uint32_t netlong);

#endif/*!ARPA_INET_H_*/
