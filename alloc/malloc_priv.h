/* Author: Christophe GUNST (christop.gh@gmail.com)
 * 
 * (implementation of an allocator for the WooKey project)
 */

#ifndef H_MALLOC_INIT
#define H_MALLOC_INIT

#include "autoconf.h"       /* For configuration options (real case) */

#ifdef CONFIG_STD_MALLOC

#include "malloc_errno.h"   /* Specific wmalloc errno values */
#include "libc/types.h"
#include "libc/malloc.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/semaphore.h"


/********************************************************************************/

/* Testing */

//#define PRINT_HEAP

#ifdef PRINT_HEAP
int print_heap(void);
#endif



/* Types and structures definitions */

typedef uint16_t u_flg_t;
# if CONFIG_STD_MALLOC_SIZE_LEN == 16
typedef uint16_t u__sz_t;
typedef uint16_t u_off_t;
typedef uint32_t u_can_t;
# elif CONFIG_STD_MALLOC_SIZE_LEN == 32
typedef uint32_t u__sz_t;
typedef uint32_t u_off_t;
typedef uint64_t u_can_t;
# endif



/* Functions prototypes */

#if CONFIG_STD_MALLOC_SIZE_LEN == 16
int wmalloc(void **ptr_to_alloc, const uint16_t len, const int flag);
#elif CONFIG_STD_MALLOC_SIZE_LEN == 32
int wmalloc(void **ptr_to_alloc, const uint32_t len, const int flag);
#endif

int wfree(void **ptr_to_free);

#if CONFIG_STD_MALLOC_INTEGRITY >= 2 
int _heap_integrity(void);
#endif


/* Block security options */

//#define _ALLOC_NORMAL        (int) 0x00000000
//#define _ALLOC_SENSITIVE     (int) 0xFFFFFFFF


/* Characters used for blanking freed and allocated blocks */

# define CHAR_ZERO              0
# define CHAR_WRITTEN           0


/* Limits for injection of random blocks at heap's initialization */

#define MIN_BETWEEN_RAND        768
#define MAX_BETWEEN_RAND        1280
#define MIN_LEN_RAND            8
#define MAX_LEN_RAND            32
#define MAX_LEN_B_0             16


/* Integrity checking */

#define CHECK_CANARI            0x0001
#define CHECK_SZ_PRV            0x0010
#define CHECK_SZ_CUR            0x0020
#define CHECK_SZ_BOTH           0x0030
#define CHECK_SZ_EQ_PRV         0x0040
#define CHECK_SZ_EQ_NXT         0x0080
#define CHECK_SZ_EQ_BOTH        0x00C0
#define CHECK_SZ_ALL            0x00F0
#define CHECK_FREE_PRV          0x0100
#define CHECK_FREE_NXT          0x0200
#define CHECK_FREE_BOTH         0x0300
#define CHECK_FREE_EQ_PRV       0x0400
#define CHECK_FREE_EQ_NXT       0x0800
#define CHECK_FREE_EQ_BOTH      0x0C00
#define CHECK_FREE_ALL          0x0F00
#define CHECK_CONSISTENCY       0x0CC0
#define CHECK_ALL_ALLOC         (CHECK_CANARI|CHECK_SZ_ALL)
#define CHECK_ALL_FREE          (CHECK_ALL_ALLOC|CHECK_FREE_ALL)
#define CHECK_BASE              0x1000


/* Integrity errors */

#define NB_INTEGRITY_ERROR      13

#define INTEGRITY_FLAG          -1
#define INTEGRITY_B_0           -2
#define INTEGRITY_CANARI        -3
#define INTEGRITY_PRV_SZ        -4
#define INTEGRITY_SZ            -5
#define INTEGRITY_PRV_FREE      -6
#define INTEGRITY_NXT_FREE      -7
#define INTEGRITY_NB_FREE       -8
#define INTEGRITY_SZ_FREE       -9
#define INTEGRITY_SZ_NEQ_PRV    -10
#define INTEGRITY_SZ_NEQ_NXT    -11
#define INTEGRITY_FREE_NEQ_PRV  -12
#define INTEGRITY_FREE_NEQ_NXT  -13


/* Alignment */

#if CONFIG_STD_MALLOC_ALIGN > 1
# define ALIGN(l)   (uint32_t) (((l) % CONFIG_STD_MALLOC_ALIGN) ? \
                                ((l) + CONFIG_STD_MALLOC_ALIGN - ((l) % CONFIG_STD_MALLOC_ALIGN)) : \
                                 (l))
#else
# define ALIGN(l)   (l)
#endif


/* Source headers */

#include "malloc_init.h"

#ifdef CONFIG_STD_MALLOC_STD
#include "malloc_ewok.h"
#endif

#ifdef CONFIG_STD_MALLOC_LIGHT
#include "malloc_light.h"
#endif

#ifdef CONFIG_STD_MALLOC_BINS
#include "malloc_bins.h"
#endif

/* For randomness source */
#include "libc/random.h"

#endif
#endif

