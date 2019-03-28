#include "api/types.h"
#include "api/regutils.h"

#include "api/arpa/inet.h"

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
    netshort = to_big32(hostshort);
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
    to_little32(netshort);
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
    to_little32(netlong);
#endif
    return hostlong;
}
