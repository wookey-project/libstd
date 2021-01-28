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
#ifndef STRING_H
#define STRING_H

/*!
 * \file string manipulation functions
 *
 * This API implement a subset of the POSIX string API,
 * with as much as possible respect for the standard
 * libstring definition as  defined in POSIX-1-2001, C09, C99,
 * SVr4 and 4.3BSD.
 */

#include "libc/types.h"

/*****************************************
 *  error handling helpers
 ****************************************/

/*
 * Not fully POSIX compliant (as no errno support) implementation of
 * strerror for syscalls return values
 */
const char *strerror(uint8_t ret);

/*****************************************
 * string manipulation functions
 *****************************************/

/*
 * Calculate the length of a NULL-terminated string.
 *
 * The length is equal to the effective number of characters, not
 * including the '\0' terminal one.
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */

/*@
  axiomatic string_len {
    logic integer strlen(char * s) reads s[0 .. ] ;

    axiom pos_or_nul{L}:
      \forall char* s, integer i ;
        (0 <= i && (\forall integer j ; 0 <= j < i ==> s[j] != '\0') && s[i] == '\0') ==>
      strlen(s) == i ;
    axiom no_end{L}:
      \forall char* s ;
        (\forall integer i ; 0 <= i ==> s[i] != '\0') ==> strlen(s) < 0 ;
  }
*/

/*@
  @ assigns \nothing;
  @ ensures s == NULL ==> \result == 0;
  @ ensures s != NULL ==> \result == strlen(\old(s));
 */
uint32_t  strlen(const char * s);

/*
 * Compare two strings
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
int       strcmp(const char * s1,
                 const char * s2);

/*
 * Compare n first bytes of two strings
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
int       strncmp(const char *s1,
                  const char *s2,
                  uint32_t    n);


/*
 * Copy content from one string to another
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * WARNING: the length of dest *MUST* be known as greater than src lenght.
 * This function does *not* handle bound checking as it is not standard conform.
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
char *    strcpy(char *       dest,
                 const char * src);
/*
 * Copy n first bytes from one string to another
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
char *    strncpy(char *      dest,
                  const char *src,
                  uint32_t    n);

/*****************************************
 * memory bytes-based manipulation function
 *****************************************/

/*
 * Copy n bytes from one memory area to another
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Beware that there is no bound checking in byte-based memory manipulation
 * functions.
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */

/*@ axiomatic MemCmp {
  @ logic ℤ memcmp{L1,L2}(char *s1, char *s2, ℤ n)
  @   reads \at(s1[0..n - 1],L1), \at(s2[0..n - 1],L2);
  @
  @ axiom memcmp_zero{L1,L2}:
  @   \forall char *s1, *s2; \forall ℤ n;
  @      memcmp{L1,L2}(s1,s2,n) == 0
  @      <==> \forall ℤ i; 0 <= i < n ==> \at(s1[i],L1) == \at(s2[i],L2);
  @
  @ }
  @*/

/*@ axiomatic MemSet {
  @ logic 𝔹 memset{L}(char *s, ℤ c, ℤ n)
  @   reads s[0..n - 1];
  @ // Returns [true] iff array [s] contains only character [c]
  @
  @ axiom memset_def{L}:
  @   \forall char *s; \forall ℤ c; \forall ℤ n;
  @      memset(s,c,n) <==> \forall ℤ i; 0 <= i < n ==> s[i] == c;
  @ }
  @*/

/*@
  predicate empty_block{L}(void *s) =
    \block_length((char*)s) == 0 && \offset((char*)s) == 0;

  predicate valid_or_empty{L}(void *s, uint32_t n) =
    (empty_block(s) || \valid_read((char*)s)) && \valid(((char*)s)+(0..n-1));

  predicate valid_read_or_empty{L}(void *s, uint32_t n) =
    (empty_block(s) || \valid_read((char*)s)) && \valid_read(((char*)s)+(1..n-1));
*/

int       memcmp(const void *  s1,
                 const void *  s2,
                 int           n);

/*@ requires valid_dest: valid_or_empty(dest, n);
  @ requires valid_src: valid_read_or_empty(src, n);
  @ requires separation:
  @   \separated(((char *)dest)+(0..n-1),((char *)src)+(0..n-1));
  @ assigns ((char*)dest)[0..n - 1] \from ((char*)src)[0..n-1];
  @ assigns \result \from dest;
  @ ensures copied_contents: memcmp{Post,Pre}((char*)dest,(char*)src,n) == 0;
  @ ensures result_ptr: \result == dest;
  @*/

void *    memcpy(void *        dest,
                 const void *  src,
                 uint32_t      n);

/*
 * Compare n first bytes of two memory areas
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */


/*
 * Set n first bytes of a given memory area with a given byte value
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */

/*@ requires valid_s: valid_or_empty(s, n);
  @ assigns ((char*)s)[0..n - 1] \from c;
  @ assigns \result \from s;
  @ ensures acsl_c_equiv: memset((char*)s,c,n);
  @ ensures result_ptr: \result == s;
  @*/

void *    memset(void *        s,
                 int           c,
                 uint32_t      n);

#endif
