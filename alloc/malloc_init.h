#ifndef H_MALLOC_INIT
#define H_MALLOC_INIT

#include "autoconf.h"

#ifdef CONFIG_STD_MALLOC

#include "malloc_priv.h"


int wmalloc_init(void);

bool is_malloc_initialized(void);

void _set_wmalloc_heap(physaddr_t *start_heap, physaddr_t *end_heap, u__sz_t *heap_size);

#if CONFIG_STD_MALLOC_INTEGRITY >= 1
void _set_wmalloc_canaries(u_can_t *can_sz, u_can_t *can_free);
#endif

#if CONFIG_STD_MALLOC_MUTEX == 1
void _set_wmalloc_semaphore(volatile uint32_t *ptr_semaphore);
#endif


#endif
#endif

