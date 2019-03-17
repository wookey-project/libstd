#ifndef PRINT_H
#define PRINT_H

#include <stdarg.h>
#include "api/types.h"

/*******************************************
 * Implementation of POSIX stdio
 *******************************************/


/****************************************
 * printf() familly
 *
 * This implementation of printf implement a subset
 * of the POSIX.1-2001 and C99 standard API.
 *
 * The following is supported:
 *
 * flag characters:
 *
 * '0'   the value should be zero-padded. This flag is allowed for any
 *       numerical value, including pointer (p).
 *       This flag *must* be followed by a numerical, decimal value specifying
 *       the size to which the value must be padded.
 *
 *  length modifier:
 *
 *  'l'      long int conversion
 *  'll'     long long int conversion
 *  'd','i'  integer signed value conversion
 *  'u'      unsigned integer value conversion
 *  'h'      short int conversion
 *  'hh'     unsigned char conversion
 *  'x'      hexadecimal value, mapped on a long integer conversion
 *  'o'      octal value, mapped on a long integer conversion
 *  'p'      pointer, word-sized unsigned integer, starting with 0x and padded
 *           with 0 up to word-length size
 *  'c'      character value conversion
 *  's'      string conversion
 *
 *  other flags characters and length modifiers are not supported,
 *  generating an immediate stop of the fmt parsing.
 *
 */

/*
 * \brief formatted printing to the standard console.
 *
 * Printing is synchronous, including a syscall execution.
 *
 * \param fmt the formated string to print
 * \return the number of characters printed on success, -1 on failure
 */
int printf(char *fmt, ...);

/*
 * formatted printing to a given buffer.
 */
uint32_t snprintf(char *dst, uint16_t len, char *fmt, ...);

uint32_t sprintf(char *dst, char *fmt, ...);

/* others, non-POSIX compliant */

void hexdump(const uint8_t *bin, uint32_t len);

void aprintf(char *fmt, ...);

void aprintf_flush(void);

#endif
