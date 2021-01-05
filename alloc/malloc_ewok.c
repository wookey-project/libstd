/* Author: Christophe GUNST (christop.gh@gmail.com)
 *
 * (implementation of an allocator for the WooKey project)
 */

#include "autoconf.h"

#ifdef CONFIG_STD_MALLOC_STD

#include "malloc_priv.h"

//#include "../inc/memfct.h"



/* Global variables */

/* Heap specifications */
static physaddr_t _start_heap;
static physaddr_t _end_heap;
static u__sz_t    _heap_size;

/* Canaries (random or not) */
static u_can_t _can_sz;
static u_can_t _can_free;

#ifdef CONFIG_STD_MALLOC_MUTEX
/* Semaphore */
static uint32_t _ptr_semaphore;
#endif


/* Static functions prototypes */
static int _update_inter_free(struct block *b_cur, struct block *b_nxt_int, u__sz_t cur_free_sz);
static int _unlink(struct block *b_cur);
static int _link(struct block *b_cur, struct block *b_0);

static void __attribute__((optimize("O0"))) *_safe_flood_char(void *dest, const char c, uint32_t n);

#if CONFIG_STD_MALLOC_INTEGRITY >= 1
static inline int check_b_0(void);
#endif

#if CONFIG_STD_MALLOC_INTEGRITY >= 2
static inline int check_free_headers(void);
#endif

#if CONFIG_STD_MALLOC_INTEGRITY == 3
static inline int check_alloc_headers(void);
#endif

#if CONFIG_STD_MALLOC_INTEGRITY != 0
static int check_hdr(struct block *b, uint16_t flag);
#endif

#if SZ_VAL_INTEGRITY == 1
static int check_sz(struct block *b, uint16_t flag);
#endif

#if FREE_PTR_INTEGRITY == 1
static int check_free(struct block *b, uint16_t flag);
#endif

#if HEADERS_INTER_CONSISTENCY == 1
static int check_consistency(struct block * b, uint16_t flag);
#endif


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
#if CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 1
    struct block *b_cur_bis     = PRV_FREE(b_0);
#endif
    struct block *b_nxt_now     = NULL;
    struct block *b_nxt_int     = NULL;

    uint8_t insered_block       = 0;

#if STD_FREEMEM_CHECK >= 1
    u__sz_t memory_available   = 0;
#endif

#ifdef CONFIG_STD_MALLOC_RANDOM
    int32_t random = (NB_FREE() ? (int32_t) (- ((uint8_t) ((uint32_t)rand() % NB_FREE()))) : 0);
#else
    int32_t random = 0;
#endif

    /* Errno is initialized to zero */
    set_malloc_errno(0);

#ifdef CONFIG_STD_MALLOC_MUTEX
    _set_wmalloc_semaphore((uint32_t *) _ptr_semaphore);

    /* Trying to lock of wmalloc usage */
    if (!semaphore_trylock(&semaphore)) {
        set_malloc_errno(EHEAPLOCKED);
        return -1;
    }
#endif

    /* Getting of heap specification values */
    _set_wmalloc_heap(&_start_heap, &_end_heap, &_heap_size);
#if (CONFIG_STD_MALLOC_INTEGRITY == 1) && (CANARIS_INTEGRITY == 1)
    _set_wmalloc_canaries(&_can_sz, &_can_free);
#endif

    /* Checking of the validity of the flag */
    if ((flag != ALLOC_NORMAL) && (flag != ALLOC_SENSITIVE)) {
        set_malloc_errno(EHEAPFLAGNOTVALID);
        goto end_error;
    }

#if CONFIG_STD_MALLOC_CHECK_IF_NULL == 1
    /* We check if the pointer has not already been allocated */
    if (*ptr_to_alloc) {
        set_malloc_errno(EHEAPALREADYALLOC);
        goto end_error;
    }
#endif

#if CONFIG_STD_MALLOC_INTEGRITY >= 2
    /* Checking of the heap's integrity */
    if (_heap_integrity() < 0) {
        set_malloc_errno(EHEAPINTEGRITY);
        goto end_error;
    }
#elif CONFIG_STD_MALLOC_BASIC_CHECKS == 1
    /* We check b_cur (and eventually b_cur_bis) are not out of range */
#  if CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 1
    if ((OFFSET(b_cur) > OFFSET_MAX) || (OFFSET(_cur_bis) > OFFSET_MAX)) {
#  elif CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 0
    if ((OFFSET(b_cur) > OFFSET_MAX)) {
#  endif
        set_malloc_errno(EHEAPINTEGRITY);
        goto end_error;
    }
#endif

    /* We check if there is free block into heap */
    if (!NB_FREE()) {
        set_malloc_errno(EHEAPFULL);
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

#if STD_FREEMEM_CHECK >= 1
    /* We check if there is definitively not enough memory for block */
    memory_available = (u__sz_t) (SZ_FREE() - (u__sz_t)(HDR_FREE_SZ * (NB_FREE() - 1)));
    if (sz > memory_available) {
        set_malloc_errno(EHEAPNOMEM);
        goto end_error;
    }
#endif

    while (1) {

#ifdef CONFIG_STD_MALLOC_RANDOM
        if (random >= 0) {
#endif

            /* We check if the current block is large enough */
#if CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 0
            if (b_cur->sz >= sz) {

                if (b_cur == b_0) {
                    b_cur = NXT_FREE(b_0);
                    continue;
                }
#elif CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 1
            if ((b_cur->sz >= sz) || (b_cur_bis->sz >= sz)) {

                if (b_cur->sz < sz) {
                    if (b_cur_bis == b_0) {
                        b_cur_bis = PRV_FREE(b_0);
                        continue;
                    }
                    b_cur = b_cur_bis;
                } else {
                    if (b_cur == b_0) {
                        b_cur = NXT_FREE(b_0);
                        continue;
                    }
                }
#endif

#if CONFIG_STD_MALLOC_INTEGRITY == 1
                /* We check the integrity of the header (if no heap integrity checking) */
                if (check_hdr(b_cur, CHECK_ALL_FREE)) {
                    set_malloc_errno(EHEAPINTEGRITY);
                    goto end_error;
                }
#endif
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
#if CANARIS_INTEGRITY == 1
                UPDATE_CANARI_SZ(b_cur);
#endif

                /* If the current block is not the last one, the next one is updated
                 * (we ensured before that there was enough space for header,
                 * else "len_bis" was increased) */
                if (cur_free_sz - sz >= HDR_FREE_SZ) {
                    b_nxt_int = (struct block *) ((physaddr_t) b_cur + sz);
                    _update_inter_free(b_cur, b_nxt_int, cur_free_sz);
                    insered_block = 1;
                } else {
                    if (_unlink(b_cur) < 0) {
                        set_malloc_errno(EHEAPNODEF);
                        goto end_error;
                    }
                    DECREASE_NB_FREE();
                }

                /* If the insered free block is not the last one (ending at _end_heap),
                 * next block's "prv_sz" is completed with the current block's size */
                if ((physaddr_t) b_nxt_now != _end_heap) {
                    b_nxt_now->prv_sz = (insered_block ? SIZE(b_nxt_int) : sz);
#if CANARIS_INTEGRITY == 1
                    UPDATE_CANARI_GENE(b_nxt_now);
#endif
                }

                /* RAZ of the whole memory reserved for new allocated block's data */
                if (flag == ALLOC_SENSITIVE) {
                    MAKE_SENSITIVE(b_cur);
                    _safe_flood_char((char *) ptr, CHAR_WRITTEN, (uint32_t) len_bis);
                } else {
                    b_cur->prv_free = 0;
                    b_cur->nxt_free = 0;
#if CANARIS_INTEGRITY == 1
                    b_cur->can_free = 0;
#endif
                }

                /* Increase the field "prv_free" of b_0 (total size of allocated memory) */
                DECREASE_SZ_FREE(sz);

#if CANARIS_INTEGRITY == 1
                /* b_0 first canari are updated for taking into account the modification of
                 * b_0->prv_sz = NB_FREE() and b_0->sz = SZ_FREE() */
                UPDATE_CANARI_SZ(b_0);
#endif

                /**********************************************************/
                /**********************************************************/
                /* HERE ALLOCATED POINTER IS SET AND 0 IS RETURNED        */
                /**********************************************************/
                *ptr_to_alloc = ptr;

#ifdef CONFIG_STD_MALLOC_MUTEX
                /* Unlocking of wmalloc usage */
                if (!semaphore_release((uint32_t *) _ptr_semaphore)) {
                    set_malloc_errno(EHEAPSEMAPHORE);
                    return -1;
                }
#endif

                return 0;
                /**********************************************************/
                /**********************************************************/
            }

#if STD_FREEMEM_CHECK == 2
            /* We check if there is definitively not enough memory for block */
# if CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 0
            memory_available -= (u__sz_t)(b_cur->sz - HDR_FREE_SZ);
# elif CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 1
            memory_available -= (u__sz_t)(b_cur->sz + b_cur_bis->sz - (u__sz_t) 2*HDR_FREE_SZ);
# endif
            if (sz > memory_available) {
                set_malloc_errno(EHEAPNOMEM);
                goto end_error;
            }
#endif
#ifdef CONFIG_STD_MALLOC_RANDOM
        }
#endif

        /* We check the validity of b_cur->nxt_free and we go to the next free block:
         * - following free block by default
         * - first free block if the end is reached and conditions not fit to stop */

#if CONFIG_STD_MALLOC_BASIC_CHECKS >= 2
        /* We check the validity of b_cur->nxt_free (and eventyally b_cur_bis->nxt_free) */
# if CONFIG_STD_MALLOC_INTEGRITY < 2
#  if CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 0
        if (b_cur->nxt_free > OFFSET_MAX) {
            set_malloc_errno(EHEAPINTEGRITY);
            goto end_error;
        }
#  elif CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 1
        if ((b_cur->nxt_free > OFFSET_MAX) || (b_cur_bis->prv_free > OFFSET_MAX)) {
            set_malloc_errno(EHEAPINTEGRITY);
            goto end_error;
        }
#  endif
# endif
#endif

        /* Random number of turns is decreased (also used if no randomization) */
#if CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 0
        b_cur = NXT_FREE(b_cur);
        ++random;
#elif CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 1
        b_cur = NXT_FREE(b_cur);
        b_cur_bis = PRV_FREE(b_cur_bis);
        random += 2;
#endif

        /* If the last free block is reached without finding convenient one, we return -1 */
        if (random >= (int32_t) NB_FREE()) {
            set_malloc_errno(EHEAPNOMEM);
            goto end_error;
        }
    }

end_error:

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Unlocking of wmalloc usage (malloc_errno is not modified in order to keep the value
     * of the initial error) */
    semaphore_release((uint32_t *) _ptr_semaphore);
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

#if CANARIS_INTEGRITY == 1
    UPDATE_CANARI_BOTH(b_nxt_int);
#endif

    /* The new free block is linked instead of the newly allocated block */
    BLOCK(b_cur->prv_free)->nxt_free = OFFSET(b_nxt_int);
    BLOCK(b_cur->nxt_free)->prv_free = OFFSET(b_nxt_int);

#if CANARIS_INTEGRITY == 1
    UPDATE_CANARI_FREE(PRV_FREE(b_nxt_int));
    UPDATE_CANARI_FREE(NXT_FREE(b_nxt_int));
#endif

    return 0;
}

/****************************************************************************************/

/* Free block to be totally occupied is unlinked */
static int _unlink(struct block *b_cur)
{
    BLOCK(b_cur->prv_free)->nxt_free = b_cur->nxt_free;
    BLOCK(b_cur->nxt_free)->prv_free = b_cur->prv_free;

#if CANARIS_INTEGRITY == 1
    UPDATE_CANARI_FREE(PRV_FREE(b_cur));
    UPDATE_CANARI_FREE(NXT_FREE(b_cur));
#endif

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
    set_malloc_errno(0);

#ifdef CONFIG_STD_MALLOC_MUTEX
    _set_wmalloc_semaphore((uint32_t *) _ptr_semaphore);

    /* Locking of wmalloc usage */
    if (!semaphore_trylock(&semaphore)) {
        set_malloc_errno(EHEAPLOCKED);
        return -1;
    }
#endif

    /* Getting of heap specification values */
    _set_wmalloc_heap(&_start_heap, &_end_heap, &_heap_size);
#if (CONFIG_STD_MALLOC_INTEGRITY == 1) && (CANARIS_INTEGRITY == 1)
    _set_wmalloc_canaries(&_can_sz, &_can_free);
#endif

    /* We check if the pointer is not null */
    if (!(*ptr_to_free)) {
        set_malloc_errno(EHEAPALREADYFREE);
        goto end_error;
    }

    /* We check if the pointer is not out of range */
    if (((struct alloc_block *) (*ptr_to_free) < (struct alloc_block *) b_1 + 1) ||
        ((physaddr_t) (*ptr_to_free) > _end_heap)) {
        set_malloc_errno(EHEAPOUTOFRANGE);
        goto end_error;
    }

    /* We get the block structure address from the pointer to be freed;
     * at the end of the function, b_cur will correspond with the free block,
     * in taking into account the eventual merging with previous and/or next frees blocks
     */
    b_cur = (struct block *) ((struct alloc_block *) (*ptr_to_free) - 1);

    /* We check if the block has not already been freed */
    if (IS_FREE(b_cur)) {
        set_malloc_errno(EHEAPINTEGRITY);
        goto end_error;
    }

#if CONFIG_STD_MALLOC_INTEGRITY >= 2
    /* Checking of the heap's integrity */
    if (_heap_integrity() < 0) {
        set_malloc_errno(EHEAPINTEGRITY);
        goto end_error;
    }
#elif CONFIG_STD_MALLOC_INTEGRITY == 1
    /* We check the integrity of the header (if no heap integrity checking) */
    if (check_hdr(b_cur, CHECK_ALL_ALLOC)) {
        set_malloc_errno(EHEAPINTEGRITY);
        goto end_error;
    }
#endif

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

#if CONFIG_STD_MALLOC_INTEGRITY == 1
        /* We check the integrity of the header (if no heap integrity checking) */
        if (check_hdr(b_prv, CHECK_ALL_FREE)) {
            set_malloc_errno(EHEAPINTEGRITY);
            goto end_error;
        }
#endif

        if (IS_FREE(b_prv)) {

            merged |= MERGED_WITH_PRV;

            /* Last block updated (size increased) */
            b_prv->sz = (u__sz_t) (SIZE(b_prv) + SIZE(b_cur));
#if CANARIS_INTEGRITY == 1
            UPDATE_CANARI_SZ(b_prv);
#endif

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

#if CONFIG_STD_MALLOC_INTEGRITY == 1
        /* We check the integrity of the header (if no heap integrity checking) */
        if (check_hdr(b_nxt, CHECK_ALL_FREE ^ CHECK_SZ_EQ_PRV)) {
            set_malloc_errno(EHEAPINTEGRITY);
            goto end_error;
        }
#endif

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
#if CANARIS_INTEGRITY == 1
                UPDATE_CANARI_FREE(PRV_FREE(b_cur));
#endif
            }

            b_cur->nxt_free = b_nxt->nxt_free;
            NXT_FREE(b_cur)->prv_free = OFFSET(b_cur);
#if CANARIS_INTEGRITY == 1
            UPDATE_CANARI_FREE(NXT_FREE(b_cur));
#endif

            /* RAZ of tne next block's header */
            _safe_flood_char((char *) b_nxt, CHAR_ZERO, HDR_FREE_SZ);
        }
    }

    /* Canari_1 is updated */
#if CANARIS_INTEGRITY == 1
    UPDATE_CANARI_BOTH(b_cur);
#endif

    /* If the updated block is not the final one, the next block is updated (prv_sz) */
    if (NOT_LAST_BLOCK(b_cur)) {
        ((struct block *) ((physaddr_t) b_cur + b_cur->sz))->prv_sz = b_cur->sz;
#if CANARIS_INTEGRITY == 1
        UPDATE_CANARI_SZ((struct block *)((physaddr_t) b_cur + b_cur->sz));
#endif
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
            set_malloc_errno(EHEAPNODEF);
            goto end_error;
        }

        /* We increase the number of free blocks */
        INCREASE_NB_FREE();
    }

end:

#if CANARIS_INTEGRITY == 1
    /* b_0 first canari are updated for taking into account the modification of
     * b_0->prv_sz = NB_FREE() and b_0->sz = SZ_FREE() */
    UPDATE_CANARI_SZ(b_0);
#endif

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Unlocking of wmalloc usage */
    if (!semaphore_release((uint32_t *) _ptr_semaphore)) {
        set_malloc_errno(EHEAPSEMAPHORE);
        return -1;
    }
#endif

    return 0;

end_error:

#ifdef CONFIG_STD_MALLOC_MUTEX
    /* Unlocking of wmalloc usage (malloc_errno is not modified in order to keep the value
     * of the initial error) */
    semaphore_release((uint32_t *) _ptr_semaphore);
#endif

    return -1;
}

/****************************************************************************************/


static int _link(struct block *b_cur, struct block *b_0)
{
    struct block *b_prv = b_0;
    struct block *b_nxt = b_0;

    u_off_t o_cur = OFFSET(b_cur);

#if CONFIG_STD_MALLOC_INTEGRITY == 0
# if CONFIG_STD_MALLOC_BASIC_CHECKS >= 1
    if ((b_0->nxt_free > OFFSET_MAX) || (b_0->prv_free > OFFSET_MAX)) {
        set_malloc_errno(EHEAPINTEGRITY);
        return -1;
    }
# endif
#endif

    /* We look for the first free block after the new one */
# if CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 0
    while ((b_prv->nxt_free < o_cur) && (b_prv->nxt_free != 0)) {
        b_prv = NXT_FREE(b_prv);
    }
    b_nxt = NXT_FREE(b_prv);
# elif CONFIG_STD_MALLOC_DBLE_WAY_SEARCH == 1
    while (((b_prv->nxt_free < o_cur) && (b_prv->nxt_free != 0)) &&
            (b_nxt->prv_free > o_cur)) {
        b_prv = NXT_FREE(b_prv);
        b_nxt = PRV_FREE(b_nxt);
    }

    if (b_prv->nxt_free > o_cur) {
        b_nxt = NXT_FREE(b_prv);
    } else {
        b_prv = PRV_FREE(b_nxt);
    }
# endif

    /* Current free block is updated */
    b_cur->prv_free = b_nxt->prv_free;
    b_cur->nxt_free = b_prv->nxt_free;

    /* Previous ant nxt free block are updated */
    b_prv->nxt_free = o_cur;
    b_nxt->prv_free = o_cur;

#if CANARIS_INTEGRITY != 0
    /* Canaris are updated */
    UPDATE_CANARI_FREE(b_cur);
    UPDATE_CANARI_FREE(b_prv);
    UPDATE_CANARI_FREE(b_nxt);
#endif

    return 0;
}


/****************************************************************************************/
/****************************************************************************************/
/****************************************************************************************/

//#pragma GCC push_options
//#pragma GCC optimize("O0")
static void __attribute__((optimize("O0"))) *_safe_flood_char(void *dest, const char c, uint32_t n)
{
    char *byte = (char*) dest;

    while (n) {
        *byte = c;
        ++byte;
        --n;
    }

    return dest;
}
//#pragma GCC pop_options


/****************************************************************************************/
/****************************************************************************************/
/****************************************************************************************/

/****************************************************************************************/
/*  Checking of the heap's integrity                                                    */
/****************************************************************************************/
#if CONFIG_STD_MALLOC_INTEGRITY >= 2
int _heap_integrity(void)
{
    struct block *b_0   = (struct block *) _start_heap;
    struct block *b_cur = b_0 + 1;

    int error           = 0;

    /* We check the integrity of the initial block's header */
    if ((error = check_b_0())) {
        goto out;
    }

    /* All free block headers are checked, and if specified, free memory size and
     * nb free blocks are checked */
    if ((error = check_free_headers())) {
        goto out;
    }

#if CONFIG_STD_MALLOC_INTEGRITY == 3
    /* All allocated block headers are checked */
    if ((error = check_alloc_headers())) {
        goto out;
    }
#endif

out:

    return error;
}
#endif

/****************************************************************************************/

#if CONFIG_STD_MALLOC_INTEGRITY >= 1
static inline int check_b_0(void)
{
    struct block *b_0 = (struct block *) _start_heap;

    int error = 0;

    if ((error = check_hdr(b_0, CHECK_CANARI|CHECK_FREE_ALL)) ||
        (NB_FREE() > _start_heap + (_heap_size / HDR_FREE_SZ)) ||
        (SZ_FREE() > _heap_size - HDR_FREE_SZ)) {

        error = (error ? error : INTEGRITY_B_0);
    }

    return error;
}
#endif

/****************************************************************************************/

#if CONFIG_STD_MALLOC_INTEGRITY >= 2
static inline int check_free_headers(void)
{
    struct block *b_0   = (struct block *) _start_heap;
    struct block *b_cur = b_0;

#if CHECK_NB_AND_SZ == 1
    u__sz_t nb_free     = 0;
    u__sz_t sz_free     = 0;
#endif

    int error = 0;

    while ((b_cur = NXT_FREE(b_cur)) != b_0) {

        if (b_cur > (struct block *) _end_heap - 1) {
            error = INTEGRITY_NXT_FREE;
            goto out;
        }

        if (IS_ALLOC(b_cur)) {
            error = INTEGRITY_FLAG;
            goto out;
        }

        if ((error = check_hdr(b_cur, CHECK_ALL_FREE))) {
            goto out;
        }

#if CHECK_NB_AND_SZ == 1
        /* The number of free blocks is increased */
        ++nb_free;
        sz_free = (u__sz_t) (sz_free + SIZE(b_cur));
        if (nb_free > NB_FREE()) {
            error = INTEGRITY_NB_FREE;
            goto out;
        }
        if (sz_free > SZ_FREE()) {
            error = INTEGRITY_SZ_FREE;
            goto out;
        }
    }

    /* We check the equality between the number of free blocks indicated in b_0's "prv_sz"
     * and the number calculated */
    if (nb_free != NB_FREE()) {
        error = INTEGRITY_NB_FREE;
        goto out;
    }
    if (sz_free != SZ_FREE()) {
        error = INTEGRITY_SZ_FREE;
        goto out;
    }
#else
    }
#endif

out:

    return error;
}
#endif

/****************************************************************************************/

#if CONFIG_STD_MALLOC_INTEGRITY == 3
static inline int check_alloc_headers(void)
{
    struct block *b_0   = (struct block *) _start_heap;
    struct block *b_cur = b_0 + 1;

    int error           = 0;

    while ((physaddr_t) b_cur != _end_heap) {

        /* We check the integrity of the current block's header (if not free) */
        if (IS_ALLOC(b_cur)) {
            if ((error = check_hdr(b_cur, CHECK_ALL_ALLOC))) {
                goto out;
            }
        }

#if (CANARIS_INTEGRITY + SZ_VAL_INTEGRITY) == 0
        if (SIZE_SECU(b_cur) == 0) {
            error = INTEGRITY_SZ;
            goto out;
        }

        /* Next "current block" to check */
        b_cur = NEXT_SECU(b_cur);
#else
        /* Next "current block" to check */
        b_cur = NEXT(b_cur);
#endif
    }

out:

    return error;
}
#endif

/****************************************************************************************/

#if CONFIG_STD_MALLOC_INTEGRITY != 0
/* Static function for header checking (canaris, size and free fields) */
static int check_hdr(struct block *b, u__sz_t flag)
{
    int error = 0;

    /* Checking of the flag */
    if (BAD_FLAG(b)) {
        return INTEGRITY_FLAG;
    }

#if CANARIS_INTEGRITY == 1
    if (flag & CHECK_CANARI) {
        if (BAD_CANARI(b)) {
            return INTEGRITY_CANARI;
        }
    }
#endif

#if SZ_VAL_INTEGRITY == 1
    if (flag & CHECK_SZ_BOTH) {
        if ((error = check_sz(b, flag))) {
            return error;
        }
    }
#endif

#if FREE_PTR_INTEGRITY == 1
    if (flag & CHECK_FREE_BOTH) {
        if ((error = check_free(b, flag))) {
            return error;
        }
    }
#endif

#if HEADERS_INTER_CONSISTENCY == 1
    if (flag & CHECK_CONSISTENCY) {
        if ((error = check_consistency(b, flag))) {
            return error;
        }
    }
#endif

    return error;

    /* If flag not used... */
    return (int) flag;
}
#endif

/****************************************************************************************/

/* Static function for previous and current sizes checking */
#if SZ_VAL_INTEGRITY == 1
static int check_sz(struct block *b, uint16_t flag)
{
    if (flag & CHECK_SZ_PRV) {
        if ((PRV_SIZE(b) > OFFSET(b)) ||
                (PRV_SIZE(b) < HDR_FREE_SZ)) {
            return INTEGRITY_PRV_SZ;
        }
    }

    if (flag & CHECK_SZ_CUR) {
        if (((uint32_t) (OFFSET(b) + SIZE(b)) > (uint32_t) _end_heap) ||
                (SIZE(b) < HDR_FREE_SZ)) {
            return INTEGRITY_SZ;
        }
    }

    return 0;
}
#endif

/****************************************************************************************/

/* Static function for previous and next free pointers checking */
#if FREE_PTR_INTEGRITY == 1
static int check_free(struct block *b, uint16_t flag)
{
    if (IS_ALLOC(b)) {
        return 0;
    }

    if (flag & CHECK_FREE_PRV) {
        if ((b->prv_free > OFFSET_MAX) ||
                ((PRV_FREE(b) + 1 > b) && ((physaddr_t)b != _start_heap))) {
            return INTEGRITY_PRV_FREE;
        }
    }

    if (flag & CHECK_FREE_NXT) {
        if ((b->nxt_free > OFFSET_MAX) ||
                ((NXT_FREE(b) < b + 1) && (b->nxt_free != 0))) {
            return INTEGRITY_NXT_FREE;
        }
    }

    return 0;
}
#endif

/****************************************************************************************/

/* Static function for inter-consistency checking */
#if HEADERS_INTER_CONSISTENCY == 1
static int check_consistency(struct block * b, u__sz_t flag)
{
    if (flag & CHECK_SZ_EQ_PRV) {
        if (NOT_FIRST_BLOCK(b)) {
# if CANARIS_INTEGRITY == 0
            if (b->prv_sz != SIZE(PREV_SECU(b))) {
# else
            if (b->prv_sz != SIZE(PREV(b))) {
# endif
                return INTEGRITY_SZ_NEQ_PRV;
            }
        }
    }

    if (flag & CHECK_SZ_EQ_NXT) {
        if (NOT_LAST_BLOCK(b)) {
# if CANARIS_INTEGRITY == 0
            if (SIZE(b) != NEXT_SECU(b)->prv_sz) {
# else
            if (SIZE(b) != NEXT(b)->prv_sz) {
# endif
                return INTEGRITY_SZ_NEQ_NXT;
            }
        }
    }

    if (IS_ALLOC(b)) {
        return 0;
    }

    if (flag & CHECK_FREE_EQ_PRV) {
# if CANARIS_INTEGRITY == 0
        if (NXT_FREE_SECU((PRV_FREE_SECU(b))) != b) {
# else
        if (NXT_FREE(PRV_FREE(b)) != b) {
# endif
            return INTEGRITY_FREE_NEQ_PRV;
        }
    }

    if (flag & CHECK_FREE_EQ_NXT) {
# if CANARIS_INTEGRITY == 0
        if (PRV_FREE_SECU(NXT_FREE_SECU(b)) != b) {
# else
        if (PRV_FREE(NXT_FREE(b)) != b) {
# endif
            return INTEGRITY_FREE_NEQ_NXT;
        }
    }

    return 0;
}
#endif


/****************************************************************************************/
/****************************************************************************************/
/****************************************************************************************/


#ifdef PRINT_HEAP
int print_heap(void)
{
    struct block *b_0 = (struct block *) _start_heap;
    struct block *b_cur = NULL;

#if CONFIG_STD_MALLOC_INTEGRITY >= 2
    int8_t res_integrity = 0;

    /* Checking of the heap's integrity */
    if ((res_integrity = _heap_integrity()) < 0) {
        printf("\n\rIntegrity: NOK\n\r");
        printf("b_0->sz = %d\n\r", b_0->sz);
        return -1;
    }
#endif

    printf("Integrity: OK\n\r-----\n\r");

    printf("%x  _start_heap\n\r", _start_heap);

    b_cur = b_0;

    while ((physaddr_t) b_cur < _end_heap) {

        printf("%x", (physaddr_t) b_cur);

        if IS_ALLOC(b_cur) {
            printf("    allocated  ");
        } else {
            if (b_cur != b_0) {
                printf("    free       ");
            } else {
                printf("    blocked    ");
            }
        }

        printf("%6d", SIZE(b_cur));
        if (SIZE(b_cur)) {
            printf(" bytes");
        } else {
            printf(" byte");
        }

        printf("\n\r");

        b_cur = NEXT(b_cur);
    }

    printf("%x  _end_heap\n\r", _end_heap);

    return 0;
}
#endif


#endif

