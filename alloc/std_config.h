/* Author: Christophe GUNST (christop.gh@gmail.com)
 * 
 * (implementation of an allocator for the WooKey project)
 */

#ifndef H_STD_CONFIG
#define H_STD_CONFIG


/********************************************************************************
 *  Testing options
 */

//#define MALLOC_TESTING

#ifdef MALLOC_TESTING
# define WOO_MALLOC_TESTING
#else
# include "tests.h"
# ifndef WOO_MALLOC_TESTING
#  ifdef GNU_MALLOC_TESTING
#   include <stdlib.h>
#  else
#   include "benchmarks.h"
#   include "types.h"
#   if MALLOC_TEST_MODE == 4
#    include <stdlib.h>
      typedef uint16_t u__sz_t;
#   endif
#  endif
    void *(*malloc_fct)(size_t len);
    void (*free_fct)(void *p);
# endif
#endif


/********************************************************************************
 *  Protections
 */

//#define SET_PROTEC_HEAP


/********************************************************************************
 *  Dynamic allocator
 */

/* Malloc mode */
#define HEAP_EWOK
//#define HEAP_WITH_CANARIS
//#define HEAP_WITH_BINS
//#define HEAP_WITH_MASKS
//#define HEAP_WITH_BITMAP

/* General specifications */

#define HEAP_SIZE_LEN               16  /* Must be equal to 16 bits or 32 bits: used for
                                           sizes and offsets fields lenght in chunks headers */
#define HEAP_ALIGN                  1   /* If not null, blocks' sizes will be aligned on
                                           this value (in bytes) */

/* Optimisation */

#define DOUBLE_WAY_SEARCH           0   /* Way for searching a fit free block:
                                           0 - heap is read only from start
                                           1 - heap is read from start and from end in the
                                               same time in order to find a fit free block
                                               more rapidly (0 else)
                                           2 - heap is read from start and end alternatively
                                               [NOT WORKING] */
#define FREE_MEMORY_CHECK           0   /* Check the real available memory:
                                           0 - never
                                           1 - when starting malloc()
                                           2 - also after each free block read */

/* Protection elements */

#define MALLOC_LOCKING              1   /* If 1, heap management is locked during each call to
                                           functions malloc() and free() so that only one thread
                                           can modify heap structure at the same time */
#define CHECK_IF_NO_INTEGRITY       1   /* If no integrity checking option:
                                           0 - no checking at all (risked)
                                           1 - checking that b_0->prv_free and b_0->nxt
                                               are not out of range
                                           2 - checking that every header to be read is not
                                               out of range */
#define HEAP_NB_CANARIS             2   /* Define the number of canaries if CANARIS_INTEGRITY
                                           option is defined: 1 or 2 (0 else) */
#define CHECK_PTR_NULL              0   /* At malloc(), pointer in argument is checked:
                                           if not null (possibly already allocated), the
                                           function returns -1 with malloc_errno = EHEAPALREADYALLOC */

/* Integrity checking mode */

#define HEAP_INTEGRITY_CHECKING     1   /* Define the mode of integrity checking:
                                           0 - no integrity checking
                                           1 - integrity checking of each header to be read
                                           2 - integrity of all free blocks' headers at each
                                               malloc() and free() (quite expensive...)
                                           3 - IDEM but with allocated blocks' headers
                                               (even more expensive...) */


#ifdef MALLOC_TESTING
# undef  HEAP_INTEGRITY_CHECKING
# define HEAP_INTEGRITY_CHECKING    3
#endif


/* Integrity checking options */

#if HEAP_INTEGRITY_CHECKING >= 1

# define CANARIS_INTEGRITY          1
# define FREE_PTR_INTEGRITY         0
# define SZ_VAL_INTEGRITY           0
# define HEADERS_INTER_CONSISTENCY  0
# define CHECK_NB_AND_SZ            1

# define SUM_VERSION                2

#endif


/* Zeroification */

//#define ZERO_FREED_BLOCK
//#define ZERO_ALLOCATED_BLOCK



/* Randomization */

//#define RANDOM_ALLOCATION   /* Free blocks are not fill up automatically from the begining */
//
//#define RANDOM_CANARIS      /* Canaries have random values */
//#define RANDOM_INIT_CHUNKS  /* Frozen blocks placed through the heap at starting */
//#define RANDOM_B_0_SIZE     /* Initial block (not allocatable) with random size */
//#define FLAG_SUM            /* Flag is XORed with b->prv_sz and b->sz */



#ifndef MALLOC_TESTING
# if CANARIS_INTEGRITY + \
    FREE_PTR_INTEGRITY + \
    SZ_VAL_INTEGRITY + \
    HEADERS_INTER_CONSISTENCY + \
    CHECK_NB_AND_SZ == 0
#  undef  HEAP_INTEGRITY_CHECKING
#  define HEAP_INTEGRITY_CHECKING   0
# endif
#else
# if HEAP_INTEGRITY_CHECKING == 0
#  undef  HEAP_INTEGRITY_CHECKING
#  define HEAP INTEGRITY_CHECKING   3
# endif
#endif


#if (CANARIS_INTEGRITY + \
    FREE_PTR_INTEGRITY + \
    SZ_VAL_INTEGRITY + \
    HEADERS_INTER_CONSISTENCY == 0) && \
    (CHECK_NB_AND_SZ == 1) && \
    (HEAP_INTEGRITY_CHECKING == 3)
# undef  HEAP_INTEGRITY_CHECKING
# define HEAP_INTEGRITY_CHECKING    2
#endif


#ifdef CANARIS_INTEGRITY
# if HEAP_NB_CANARIS == 0
#  error "Canari checking needs at least one canari!"
# endif
#endif


#endif
