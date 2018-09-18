#include "autoconf.h"

#ifdef CONFIG_STD_MALLOC

#include "malloc_priv.h"


//#include "../inc/memfct.h"


/* Global variables */

/* Extern global variables */
extern uint32_t _s_bss;
extern uint32_t _e_bss;
extern uint32_t _s_data;
extern uint32_t _e_data;
extern uint32_t _s_stack;
extern uint32_t _e_stack;
extern uint32_t numslots;

/* Heap specifications */
static physaddr_t _start_heap;
static physaddr_t _end_heap;
static u__sz_t    _heap_size;

#if CONFIG_STD_MALLOC_INTEGRITY >= 1
/* Canaries (random or not) */
static u_can_t _can_sz;
static u_can_t _can_free;
#endif

#ifdef CONFIG_STD_MALLOC_MUTEX
/* Semaphore */
static volatile uint32_t _semaphore;
#endif


/* Static functions prototypes */
static int _wmalloc_init(physaddr_t const task_start_heap, uint32_t const task_heap_size);


/****************************************************************************************/
/****************************************************************************************/
/****************************************************************************************/


/* Set heap specifications for allocator functions */
void _set_wmalloc_heap(physaddr_t *start_heap, physaddr_t *end_heap, u__sz_t *heap_size)
{
    *start_heap = _start_heap;
    *end_heap   = _end_heap;
    *heap_size  = _heap_size;

    return;
}


#if CONFIG_STD_MALLOC_INTEGRITY >= 1
/* Set heap specifications for allocator functions */
void _set_wmalloc_canaries(u_can_t *can_sz, u_can_t *can_free)
{
    *can_sz   = _can_sz;
    *can_free = _can_free;

    return;
}
#endif


#ifdef CONFIG_STD_MALLOC_MUTEX
/* Set semaphore for allocator functions */
void _set_wmalloc_semaphore(volatile uint32_t *ptr_semaphore)
{
    *ptr_semaphore = (physaddr_t) (&_semaphore);

    return;
}
#endif


/****************************************************************************************/
/*  Initialization of heap global variables                                             */
/****************************************************************************************/
int wmalloc_init(void)
{
    physaddr_t task_start_heap = 0;
    uint32_t   task_heap_size  = 0;

#ifdef CONFIG_KERNEL_EWOK
    task_start_heap = (physaddr_t) (&_e_bss);

    task_heap_size  = (uint32_t) (((uint32_t) CONFIG_RAM_SLOT_SIZE * (uint32_t) &numslots) - \
                                  ((uint32_t) &_e_stack - (uint32_t) &_s_stack) - \
                                  ((uint32_t) &_e_data  - (uint32_t) &_s_data) - \
                                  ((uint32_t) &_e_bss   - (uint32_t) &_s_bss));
#if 1 /* for debug purpose */
    printf("heap start: %x\n", task_start_heap);
    printf("heap size: %x\n", task_heap_size);
    printf("num slots: %x\n", &numslots);
    printf("data start: %x\n", &_s_data);
    printf("data end: %x\n", &_e_data);
    printf("bss start: %x\n", &_s_bss);
    printf("bss end: %x\n", &_e_bss);
    printf("stack start: %x\n", &_s_stack);
    printf("stack end: %x\n", &_e_stack);
#endif

#ifdef CONFIG_STD_MALLOC_LIGHT
    malloc_light_init(task_start_heap, (physaddr_t)task_start_heap + task_heap_size, (u__sz_t)task_heap_size);
#else
# error "init for other malloc not done yet"
#endif

#else
# error "not a supported allocator backend"
#endif
    
    /* If no kernel specified... */
    if ((!task_start_heap) || (!task_heap_size)) {
        return -1;
    }

    return _wmalloc_init(task_start_heap, task_heap_size);
}


/****************************************************************************************/
/*  Initialization of heap global variables                                             */
/****************************************************************************************/
static int _wmalloc_init(const physaddr_t task_start_heap, const uint32_t task_heap_size)
{
    uint32_t heap_size_tmp = task_heap_size;

    struct block *b_0 = NULL;
    struct block *b_1 = NULL;

    errno = 0;
    
    /* Size validity is checked */
#if CONFIG_STD_MALLOC_SIZE_LEN == 16
    if (heap_size_tmp > 65535) {
        errno = EHEAPSIZETOOBIG;
        return -1;
    }
#endif

#if CONFIG_STD_MALLOC_ALIGN > 1
    heap_size_tmp = ALIGN(heap_size_tmp);
#endif
    
    if (heap_size_tmp < 2 * HDR_FREE_SZ) {
        errno = EHEAPSIZETOOSMALL;
        return -1;
    }

    /* Static global variables are set */
    _start_heap = (physaddr_t) task_start_heap;
    _heap_size  = (u__sz_t)    task_heap_size;
    _end_heap   = (physaddr_t) (task_start_heap + task_heap_size);

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Locking of wmalloc usage */
    semaphore_init(1, &_semaphore);

    /* Trying to lock of wmalloc usage */
    if (!semaphore_trylock(&_semaphore)) {
        errno = EHEAPLOCKED;
        return -1;
    }

#endif

    /* Definition of canaries */
#if CANARIS_INTEGRITY == 1
# ifdef RANDOM_CANARIS
    _can_sz     = (u_can_t) rand();
    _can_free   = (u_can_t) rand();
# else
    _can_sz     = (u_can_t) 0xF0F0F0F0;
    _can_free   = (u_can_t) 0x0F0F0F0F;
# endif
#endif

    /* Definition of the initial block of the heap */
    b_0             = (struct block *) _start_heap;

    /* Setting of the block structure 0 */
    b_0->prv_sz     = 1;                                    /* Number of free blocks */
    b_0->sz         = (u__sz_t) (_heap_size - HDR_FREE_SZ); /* Free memory */
    b_0->flag       = 0;
    b_0->prv_free   = HDR_FREE_SZ;
    b_0->nxt_free   = HDR_FREE_SZ;
# if CANARIS_INTEGRITY == 1
    UPDATE_CANARI_BOTH(b_0);
# endif

    /* Definition of the first block which can be allocated */
    b_1 = b_0 + 1;

    /* Setting of the block 1 (the first one which can be allocated) */
    b_1->prv_sz     = HDR_FREE_SZ;
    b_1->sz         = (u__sz_t) (_heap_size - HDR_FREE_SZ);
    b_1->flag       = 0;
    b_1->prv_free   = 0;
    b_1->nxt_free   = 0;
# if CANARIS_INTEGRITY == 1
    UPDATE_CANARI_BOTH(b_1);
# endif

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Unlocking of wmalloc usage */
    if (!semaphore_release(&_semaphore)) {
        errno = EHEAPSEMAPHORE;
        return -1;
    }
#endif

    return 0;
}


#endif

