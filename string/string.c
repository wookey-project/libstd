#include "string.h"
#include "print.h"
#include "api/syscall.h"

#include "print_priv.h"

#define UNDEFINED_BEHAVIOR_INT_VALUE 42
#define UNDEFINED_BEHAVIOR_STR_VALUE NULL

static const char *strerror_tab[4] = {
    "Done", //"Done: Syscall finished successfully",
    "Inval", //"Inval: user informations are not valid",
    "Denied", //"Denied: not the good time or access prohibed",
    "Busy", //"Busy: already used or not enough space to use",
};

/***********************************************
 * libstring API implementation
 **********************************************/

/*
 * Not fully POSIX compliant (as no errno support) implementation of
 * strerror for syscalls return values
 */
const char *strerror(uint8_t ret)
{
    if (ret < SYS_E_MAX) {
        return strerror_tab[ret];
    }
    return 0;
}

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
uint32_t strlen(const char *s)
{
    uint32_t i = 0;

    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!s) {
        return UNDEFINED_BEHAVIOR_INT_VALUE;
    }

    while (*s) {
        i++;
        s++;
    }
    return i;
}

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
int strcmp(const char *s1, const char *s2)
{
    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!s1 || !s2) {
        return UNDEFINED_BEHAVIOR_INT_VALUE;
    }

    for (uint32_t i = 0; s1[i] != '\0' && s2[i] != '\0'; ++i) {
        if (s1[i] == s2[i]) {
            continue;
        } else {
            return (s1[i] - s2[i]);
        }
    }
    return 0;
}

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
int strncmp(const char *s1, const char *s2, uint32_t n)
{
    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!s1 || !s2) {
        return UNDEFINED_BEHAVIOR_INT_VALUE;
    }

    for (uint32_t i = 0; s1[i] != '\0' && s2[i] != '\0' && i < n; ++i) {
        if (s1[i] == s2[i]) {
            continue;
        } else {
            return (s1[i] - s2[i]);
        }
    }
    return 0;
}

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
char *strcpy(char *dest, const char *src)
{
    uint32_t i;

    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!dest || !src) {
        return UNDEFINED_BEHAVIOR_STR_VALUE;
    }


    /* copying up to n bytes from src */
    for (i = 0; src[i] != '\0'; i++) {
            dest[i] = src[i];
    }
    /* finishing with '\0' */
    dest[i] = src[i];

    return dest;
}


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
char *strncpy(char *dest, const char *src, uint32_t n)
{
    uint32_t i;

    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!dest || !src) {
        return UNDEFINED_BEHAVIOR_STR_VALUE;
    }

    /* copying up to n bytes from src */
    for (i = 0; i < n && src[i] != '\0'; i++) {
            dest[i] = src[i];
    }
    /* if src length is less than n, finishing with '\0' up to n */
    for ( ; i < n; i++) {
        dest[i] = '\0';
    }

    return dest;
}

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
void *memcpy(void *dest, const void *src, uint32_t n)
{
    char *d_bytes = dest;
    const char *s_bytes = src;

    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!dest || !src) {
        return UNDEFINED_BEHAVIOR_STR_VALUE;
    }


    /* Copying from source to destination. As described in POSIX and other
     * standards, memcpy considers that memory regions must not overlap.
     * As a consequence, there is no overlap check here */
    while (n) {
        *d_bytes = *s_bytes;
        d_bytes++;
        s_bytes++;
        n--;
    }
    return dest;
}

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
int memcmp(const void *s1, const void *s2, int n)
{
    unsigned char u1, u2;

    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!s1 || !s2) {
        return UNDEFINED_BEHAVIOR_INT_VALUE;
    }


    /* looping upto n == 0 */
    for (; n--; s1++, s2++) {
        u1 = *(const unsigned char *)s1;
        u2 = *(const unsigned char *)s2;
        if (u1 != u2) {
            return (u1 - u2);
        }
    }

    return 0;
}

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
void *memset(void *s, int c, uint32_t n)
{
    /* sanitation. This part can produce, as defined in the above
     * standard, an 'undefined behavior'. As a consequence, in all
     * string function, invalid input will produce, for integer
     * return, returning 42, for string return, returning NULL */
    if (!s) {
        return UNDEFINED_BEHAVIOR_STR_VALUE;
    }

    /* memseting s with c */
    char *bytes = s;
    while (n) {
        *bytes = c;
        bytes++;
        n--;
    }
    return s;
}

