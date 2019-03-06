#include "autoconf.h"

#ifdef CONFIG_STD_MALLOC_LIGHT

#include "malloc_priv.h"
#include "malloc_init.h"

//#include "../inc/memfct.h"


/* Global variables */

/* Heap specifications */
static physaddr_t _start_heap;
static physaddr_t _end_heap;
static u__sz_t    _heap_size;

#ifdef CONFIG_STD_MALLOC_MUTEX
/* Semaphore */
volatile uint32_t _ptr_semaphore;
#endif


/* Static functions prototypes */
static int _update_inter_free(struct block *b_cur, struct block *b_nxt_int, u__sz_t cur_free_sz);
static int _unlink(struct block *b_cur);
static int _link(struct block *b_cur, struct block *b_0);

static void *_safe_flood_char(void *dest, const char c, uint32_t n);

/*
 * This function should be called by malloc_init() to
 * initialize local heap informations
 */
void malloc_light_init(physaddr_t start_heap,
                       physaddr_t end_heap,
                       u__sz_t    heap_size)
{
    _start_heap = start_heap;
    _end_heap = end_heap;
    _heap_size = heap_size;

#ifdef CONFIG_STD_MALLOC_MUTEX
    _set_wmalloc_semaphore((uint32_t *) _ptr_semaphore);
#endif
}

/*********************************************************************************************/
/*  Malloc() function                                                                        */
/*********************************************************************************************/
#if CONFIG_STD_MALLOC_SIZE_LEN == 16
int wmalloc(void **ptr_to_alloc, const uint16_t len, const int flag)
#elif CONFIG_STD_MALLOC_SIZE_LEN == 32
int wmalloc(void **ptr_to_alloc, const uint32_t len, const int flag)
#endif
{
    void *ptr                   = NULL;

    u__sz_t len_bis             = (u__sz_t) len;
    u__sz_t sz                  = 0;
    u__sz_t cur_free_sz         = 0;

    struct block *b_0 = (struct block *) _start_heap;
    struct block *b_cur         = NXT_FREE(b_0);
    struct block *b_nxt_now     = NULL;
    struct block *b_nxt_int     = NULL;

    uint8_t insered_block       = 0;

    int32_t random = 0;

    /* Errno is initialized to zero */
    malloc_errno = 0;

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Trying to lock of wmalloc usage */
    if (!semaphore_trylock(&_ptr_semaphore)) {
        malloc_errno = EHEAPLOCKED;
        return -1;
    }
#endif

    /* Getting of heap specification values */
    //_set_wmalloc_heap(&_start_heap, &_end_heap, &_heap_size);

    /* Checking of the validity of the flag */
    if ((flag != ALLOC_NORMAL) && (flag != ALLOC_SENSITIVE)) {
        malloc_errno = EHEAPFLAGNOTVALID;
        goto end_error;
    }

    /* We check if there is free block into heap */
    if (!NB_FREE()) {
        malloc_errno = EHEAPFULL;
        goto end_error;
    }

    /* Allocated block cannot be smaller than a free bock header (think free()...) */
    if (len_bis < (u__sz_t) (HDR_FREE_SZ - HDR_SZ)) {
        len_bis = (u__sz_t) (HDR_FREE_SZ - HDR_SZ);
    }

#if CONFIG_STD_MALLOC_ALIGN > 1
    /* The asked length is aligned */
    len_bis = ALIGN(len_bis);
#endif

    /* Block size is calculated */
    sz = (u__sz_t) (len_bis + HDR_SZ);

    while (1) {

        /* We check if the current block is large enough */
        if (b_cur->sz >= sz) {

            if (b_cur == b_0) {
                b_cur = NXT_FREE(b_0);
                continue;
            }

            /* Size of the current free block */
            cur_free_sz = b_cur->sz;

            /* The present next block is defined */
            b_nxt_now = NEXT(b_cur);

            /* Pointer to be returned by malloc() */
            ptr  = (void *) ((struct alloc_block *) b_cur + 1);

            /* If the space after the block to allocate is too small to allocate
             * another block (it needs at least enough space for header + 1 byte) */
            if (cur_free_sz - sz < HDR_FREE_SZ) {
                sz = cur_free_sz;
            }

            /* Current free block is updated and changed to allocated block */
            b_cur->sz = sz;
            MAKE_ALLOC(b_cur);

            /* If the current block is not the last one, the next one is updated
             * (we ensured before that there was enough space for header,
             * else "len_bis" was increased) */
            if (cur_free_sz - sz >= HDR_FREE_SZ) {
                b_nxt_int = (struct block *) ((physaddr_t) b_cur + sz);
                _update_inter_free(b_cur, b_nxt_int, cur_free_sz);
                insered_block = 1;
            } else {
                if (_unlink(b_cur) < 0) {
                    malloc_errno = EHEAPNODEF;
                    goto end_error;
                }
                DECREASE_NB_FREE();
            }

            /* If the insered free block is not the last one (ending at _end_heap),
             * next block's "prv_sz" is completed with the current block's size */
            if ((physaddr_t) b_nxt_now != _end_heap) {
                b_nxt_now->prv_sz = (insered_block ? SIZE(b_nxt_int) : sz);
            }

            /* RAZ of the whole memory reserved for new allocated block's data */
            if (flag == ALLOC_SENSITIVE) {
                MAKE_SENSITIVE(b_cur);
                _safe_flood_char((char *) ptr, CHAR_WRITTEN, (uint32_t) len_bis);
            } else {
                b_cur->prv_free = 0;
                b_cur->nxt_free = 0;
            }

            /* Increase the field "prv_free" of b_0 (total size of allocated memory) */
            DECREASE_SZ_FREE(sz);

            /**********************************************************/
            /**********************************************************/
            /* HERE ALLOCATED POINTER IS SET AND 0 IS RETURNED        */
            /**********************************************************/
            *ptr_to_alloc = ptr;

#ifdef CONFIG_STD_MALLOC_MUTEX
            /* Unlocking of wmalloc usage */
            if (!semaphore_release(&_ptr_semaphore)) {
                malloc_errno = EHEAPSEMAPHORE;
                return -1;
            }
#endif

            return 0;
            /**********************************************************/
            /**********************************************************/
        }

        /* We check the validity of b_cur->nxt_free and we go to the next free block:
         * - following free block by default
         * - first free block if the end is reached and conditions not fit to stop */

        /* Random number of turns is decreased (also used if no randomization) */
        b_cur = NXT_FREE(b_cur);
        ++random;

        /* If the last free block is reached without finding convenient one, we return -1 */
        if (random >= (int32_t) NB_FREE()) {
            malloc_errno = EHEAPNOMEM;
            goto end_error;
        }
    }

end_error:

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Unlocking of wmalloc usage (malloc_errno is not modified in order to keep the value
     * of the initial error) */
    semaphore_release(&_ptr_semaphore);
#endif

    return -1;
}

/****************************************************************************************/

/* Intermediate free block is updated (for malloc() function) */
static int _update_inter_free(struct block *b_cur, struct block *b_nxt_int, u__sz_t cur_free_sz)
{
    b_nxt_int->flag     = 0;
    b_nxt_int->prv_sz   = b_cur->sz;
    b_nxt_int->sz       = (u__sz_t) (cur_free_sz - b_nxt_int->prv_sz);
    b_nxt_int->prv_free = b_cur->prv_free;
    b_nxt_int->nxt_free = b_cur->nxt_free;

    /* The new free block is linked instead of the newly allocated block */
    BLOCK(b_cur->prv_free)->nxt_free = OFFSET(b_nxt_int);
    BLOCK(b_cur->nxt_free)->prv_free = OFFSET(b_nxt_int);

    return 0;
}

/****************************************************************************************/

/* Free block to be totally occupied is unlinked */
static int _unlink(struct block *b_cur)
{
    BLOCK(b_cur->prv_free)->nxt_free = b_cur->nxt_free;
    BLOCK(b_cur->nxt_free)->prv_free = b_cur->prv_free;

    return 0;
}


/****************************************************************************************/
/****************************************************************************************/
/****************************************************************************************/

#define MERGED_WITH_PRV     0x01
#define MERGED_WITH_NXT     0x02
#define MERGED_WITH_BOTH    0x03


/****************************************************************************************/
/*  Free() function                                                                     */
/****************************************************************************************/
int wfree(void **ptr_to_free)
{
    struct block *b_0   = (struct block *) _start_heap;
    struct block *b_1   = b_0 + 1;

    struct block *b_cur = NULL;
    struct block *b_prv = NULL;
    struct block *b_nxt = NULL;

    uint8_t merged      = 0;

    /* Errno is initialized to zero */
    malloc_errno = 0;

#ifdef CONFIG_STD_MALLOC_MUTEX
    _set_wmalloc_semaphore(&_ptr_semaphore);

    /* Locking of wmalloc usage */
    if (!semaphore_trylock(&_ptr_semaphore)) {
        malloc_errno = EHEAPLOCKED;
        return -1;
    }
#endif

    /* Getting of heap specification values */
    _set_wmalloc_heap(&_start_heap, &_end_heap, &_heap_size);

    /* We check if the pointer is not null */
    if (!(*ptr_to_free)) {
        malloc_errno = EHEAPALREADYFREE;
        goto end_error;
    }

    /* We check if the pointer is not out of range */
    if (((struct alloc_block *) (*ptr_to_free) < (struct alloc_block *) b_1 + 1) ||
        ((physaddr_t) (*ptr_to_free) > _end_heap)) {
        malloc_errno = EHEAPOUTOFRANGE;
        goto end_error;
    }

    /* We get the block structure address from the pointer to be freed;
     * at the end of the function, b_cur will correspond with the free block,
     * in taking into account the eventual merging with previous and/or next frees blocks
     */
    b_cur = (struct block *) ((struct alloc_block *) (*ptr_to_free) - 1);

    /* We check if the block has not already been freed */
    if (IS_FREE(b_cur)) {
        malloc_errno = EHEAPINTEGRITY;
        goto end_error;
    }

    /* Block set to "free" */
    MAKE_FREE(b_cur);

    /* Decrease the field "prv_free" of b_0 (total size of allocated memory) */
    INCREASE_SZ_FREE(SIZE(b_cur));

    /* RAZ of the whole memory to free */
    if (IS_SENSITIVE(b_cur)) {
        _safe_flood_char((char *) (*ptr_to_free), CHAR_ZERO, (u__sz_t) (b_cur->sz - HDR_SZ));
        MAKE_NORMAL(b_cur);
    }

    /* Pointer to allocated block is set to 0 */
    *ptr_to_free = NULL;

    /**********************************************************************************/
    /* If the current block is not the first one (i.e the one after b_0),
     * we check if the previous block is free and thus can be merged */
    if (b_cur != b_1) {

        b_prv = PREV(b_cur);

        if (IS_FREE(b_prv)) {

            merged |= MERGED_WITH_PRV;

            /* Last block updated (size increased) */
            b_prv->sz = (u__sz_t) (SIZE(b_prv) + SIZE(b_cur));

            /* RAZ of the current block's header */
            _safe_flood_char((char *) b_cur, CHAR_ZERO, HDR_SZ);

            /* Effective merging */
            b_cur = b_prv;
        }
    }

    /**********************************************************************************/
    /* If the current block is not the final one,
     * we check if the block after is free and thus can be merged */
    if (NOT_LAST_BLOCK(b_cur)) {

        b_nxt = NEXT(b_cur);

        if (IS_FREE(b_nxt)) {

            merged |= MERGED_WITH_NXT;

            /* Current block updated (size and next_block) */
            b_cur->sz = (u__sz_t) (SIZE(b_cur) + SIZE(b_nxt));

            /* If the current block has not been already merged with the previous one
             * (condition only concerning previous block), we get the next free block's
             * "prv_free" and "nxt_free" values, and we update free block around */
            if (!(merged & MERGED_WITH_PRV)) {
                b_cur->prv_free = b_nxt->prv_free;
                PRV_FREE(b_cur)->nxt_free = OFFSET(b_cur);
            }

            b_cur->nxt_free = b_nxt->nxt_free;
            NXT_FREE(b_cur)->prv_free = OFFSET(b_cur);

            /* RAZ of tne next block's header */
            _safe_flood_char((char *) b_nxt, CHAR_ZERO, HDR_FREE_SZ);
        }
    }

    /* If the updated block is not the final one, the next block is updated (prv_sz) */
    if (NOT_LAST_BLOCK(b_cur)) {
        ((struct block *) ((physaddr_t) b_cur + b_cur->sz))->prv_sz = b_cur->sz;
    }

    /* If merged with the previous free block, no more operations to do */
    if (merged & MERGED_WITH_PRV) {
        /* The two former free blocks are merged, so number of free blocks is increased */
        if (merged & MERGED_WITH_NXT) {
            DECREASE_NB_FREE();
        }

        goto end;
    }

    /* The eventual free blocks (previous and next) are update */
    if (!merged) {

        if (_link(b_cur, b_0) < 0) {
            malloc_errno = EHEAPNODEF;
            goto end_error;
        }

        /* We increase the number of free blocks */
        INCREASE_NB_FREE();
    }

end:

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Unlocking of wmalloc usage */
    if (!semaphore_release(&_ptr_semaphore)) {
        malloc_errno = EHEAPSEMAPHORE;
        return -1;
    }
#endif

    return 0;

end_error:

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Unlocking of wmalloc usage (malloc_errno is not modified in order to keep the value
     * of the initial error) */
    semaphore_release(&_ptr_semaphore);
#endif

    return -1;
}

/****************************************************************************************/


static int _link(struct block *b_cur, struct block *b_0)
{
    struct block *b_prv = b_0;
    struct block *b_nxt = b_0;

    u_off_t o_cur = OFFSET(b_cur);

    /* We look for the first free block after the new one */
    while ((b_prv->nxt_free < o_cur) && (b_prv->nxt_free != 0)) {
        b_prv = NXT_FREE(b_prv);
    }
    b_nxt = NXT_FREE(b_prv);

    /* Current free block is updated */
    b_cur->prv_free = b_nxt->prv_free;
    b_cur->nxt_free = b_prv->nxt_free;

    /* Previous ant nxt free block are updated */
    b_prv->nxt_free = o_cur;
    b_nxt->prv_free = o_cur;

    return 0;
}


/****************************************************************************************/
/****************************************************************************************/
/****************************************************************************************/


#ifdef __GNUC__
#ifdef __clang__
# pragma clang optimize off
#else
# pragma GCC push_options
# pragma GCC optimize("O0")
#endif
#endif
static void *_safe_flood_char(void *dest, const char c, uint32_t n)
{
    char *byte = (char*) dest;

    while (n) {
        *byte = c;
        ++byte;
        --n;
    }

    return dest;
}
#ifdef __GNUC__
#ifdef __clang__
# pragma clang optimize on
#else
# pragma GCC pop_options
#endif
#endif

/****************************************************************************************/
/****************************************************************************************/
/****************************************************************************************/
#define PRINT_HEAP
#ifdef PRINT_HEAP
int print_heap(void)
{
    struct block *b_0 = (struct block *) _start_heap;
    struct block *b_cur = NULL;

    printf("\n\r%x  _start_heap\n\r", _start_heap);

    b_cur = b_0;

    while ((physaddr_t) b_cur < _end_heap) {

        printf("%x", (physaddr_t) b_cur);

        if IS_ALLOC(b_cur) {
            printf("    allocated  %d", SIZE(b_cur));
        } else {
            if (b_cur != b_0) {
                printf("    free       %d\n", SIZE(b_cur));
            } else {
                printf("    blocked    %d\n", SIZE(b_cur));
            }
        }
        b_cur = NEXT(b_cur);
    }

    printf("%x  _end_heap\n\r", _end_heap);

    return 0;
}
#endif


#endif

