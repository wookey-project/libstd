#ifndef H_MALLOC
#define H_MALLOC

#include "autoconf.h"
#include "api/types.h"

#ifdef CONFIG_STD_MALLOC


/********************************************************************************/

/* Block security options (values for flag) */

#define ALLOC_NORMAL        (int) 0x00000000
#define ALLOC_SENSITIVE     (int) 0xFFFFFFFF


/* Function prototypes */

int wmalloc_init(void);

#if CONFIG_STD_MALLOC_SIZE_LEN == 16
int wmalloc(void **ptr_to_alloc, const uint16_t len, const int flag);
#elif CONFIG_STD_MALLOC_SIZE_LEN == 32
int wmalloc(void **ptr_to_alloc, const uint32_t len, const int flag);
#endif

int wfree(void **ptr_to_free);


#endif

#endif

