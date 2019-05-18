/* Author: Christophe GUNST (christop.gh@gmail.com)
 * 
 * (implementation of an allocator for the WooKey project)
 */

#ifndef H_MALLOC_EWOK
#define H_MALLOC_EWOK

#include "autoconf.h"

#ifdef CONFIG_STD_MALLOC_STD

#include "malloc_priv.h"



/* Chunk structure :
 * - size and and previous chunk's size
 * - double linked list for free chunks : retalive pointers to previous and next free chunks
 * - pointers are relative in order to be written into uint32_t (uint16_t ?)
 */
/*#pragma pack (1)*/
struct __attribute__((packed)) block {
#if CANARIS_INTEGRITY == 1
    u_can_t can_sz;
#endif
    u_flg_t flag;
    u__sz_t prv_sz;
    u__sz_t sz;
    u_off_t prv_free;  /* Only for free blocks: relative address */
    u_off_t nxt_free;  /* Only for free blocks: relative address */
#if CANARIS_INTEGRITY == 1
    u_can_t can_free;
#endif
};

struct __attribute__((packed)) alloc_block {
#if CANARIS_INTEGRITY == 1
    u_can_t can_sz;
#endif
    u_flg_t flag;
    u__sz_t prv_sz;
    u__sz_t sz;
};



/* Chunks management */

#define OFFSET_MAX          (u__sz_t)(_heap_size - HDR_FREE_SZ)

#define OFFSET(b)           ((u_off_t) ((physaddr_t)(b) - _start_heap))
#define BLOCK(o)            ((struct block *)(_start_heap + (physaddr_t)(o)))

#define HDR_SZ              ((u__sz_t) sizeof(struct alloc_block))
#define HDR_FREE_SZ         ((u__sz_t) sizeof(struct block))

#define MASK_ALLOC          ((u_flg_t) 0x01010101)
#define MASK_FREE           ((u_flg_t) 0xFEFEFEFE)

#define IS_ALLOC(b)         (((b)->flag & MASK_ALLOC) == MASK_ALLOC)
#define IS_FREE(b)          (((b)->flag & MASK_ALLOC) == 0)

#define MAKE_ALLOC(b)       ((struct block *)(b))->flag |= MASK_ALLOC
#define MAKE_FREE(b)        ((struct block *)(b))->flag &= MASK_FREE
  
#define MASK_SENSITIVE      ((u_flg_t) 0xFEFE)
#define MASK_NORMAL         ((u_flg_t) 0x0101)

#define IS_SENSITIVE(b)     (((b)->flag & MASK_SENSITIVE) == MASK_SENSITIVE)
#define IS_NORMAL(b)        (((b)->flag & MASK_SENSITIVE) == 0)

#define MAKE_SENSITIVE(b)   ((struct block *)(b))->flag |= MASK_SENSITIVE
#define MAKE_NORMAL(b)      ((struct block *)(b))->flag &= MASK_NORMAL

#define BAD_FLAG(b)         (((((b)->flag & MASK_ALLOC) != MASK_ALLOC) && \
                              (((b)->flag & MASK_ALLOC) != 0)) || \
                             ((((b)->flag & MASK_SENSITIVE) != MASK_SENSITIVE) && \
                              (((b)->flag & MASK_SENSITIVE) != 0)))
  
#define SIZE(b)             ((b)->sz)
#define PRV_SIZE(b)         ((b)->prv_sz)

#define NEXT(b)             ((struct block *) ((physaddr_t)(b) + SIZE(b)))
#define PREV(b)             ((struct block *) ((physaddr_t)(b) - PRV_SIZE(b)))

#define PRV_FREE(b)         BLOCK((b)->prv_free)
#define NXT_FREE(b)         BLOCK((b)->nxt_free)

#define FIRST_BLOCK(b)      ((physaddr_t)(b) == (physaddr_t) (_start_heap + HDR_FREE_SZ))
#define NOT_FIRST_BLOCK(b)  ((physaddr_t)(b) != (physaddr_t) (_start_heap + HDR_FREE_SZ))
  
#define LAST_BLOCK(b)       ((physaddr_t)(b) + SIZE(b) == _end_heap)
#define NOT_LAST_BLOCK(b)   ((physaddr_t)(b) + SIZE(b) != _end_heap)

#define LAST_FREE(b)        ((b)->nxt_free == (b_0))
#define NOT_LAST_FREE(b)    ((b)->nxt_free != (b_0))

/* Only used for checking operations in order to avoid segmentation faults:
 * the inconvenience is the loss of performance */
#define SIZE_SECU(b)        ((u__sz_t) (SIZE(b) % (1 + _end_heap - (physaddr_t)(b))))
#define PRV_SIZE_SECU(b)    ((u__sz_t) ((b)->prv_sz % (1 + OFFSET(b))))
#define NEXT_SECU(b)        ((struct block *) ((physaddr_t)(b) + SIZE_SECU(b)))
#define PREV_SECU(b)        ((struct block *) ((physaddr_t)(b) - PRV_SIZE_SECU(b)))
#define PRV_FREE_SECU(b)    ((struct block *) (_start_heap + (b->prv_free % _heap_size)))
#define NXT_FREE_SECU(b)    ((struct block *) (_start_heap + (b->nxt_free % _heap_size)))



/* Canaries mamangement */

#if CANARIS_INTEGRITY == 1

#define CAN_SHIFT               HEAP_SIZE_LEN

/* Can detect most simple headers modifications */
# if SUM_VERSION == 1

#  define SUM_SZ(b)             (u_can_t) ((((u_can_t)((b)->prv_sz)) << CAN_SHIFT) ^ \
                                            ((u_can_t)((b)->sz)))

#  define SUM_FREE(b)           (u_can_t) ((((u_can_t)((b)->prv_free)) << CAN_SHIFT) ^ \
                                            ((u_can_t)((b)->nxt_free)))

#  define SUM_CAN(x,c)          ((u_can_t) (x) ^ (c))

/* More effecient, especially for detecting compensated modification of pairs of bits */
# elif SUM_VERSION == 2

#  define SUM_SZ(b)             (u_can_t) ((((u_can_t)((b)->prv_sz)) << CAN_SHIFT) ^ \
                                            ((u_can_t)((b)->sz)))

#  define SUM_FREE(b)           (u_can_t) ((((u_can_t)((b)->prv_free)) << CAN_SHIFT) ^ \
                                            ((u_can_t)((b)->nxt_free)))

#  define MIX_CAN(c)            (u_can_t) ((u_can_t)(c) ^ ((u_can_t)(c)<<5) ^ ((u_can_t)(c)>>7))

#  define SUM_CAN(x,c)          MIX_CAN(((u_can_t) (x) ^ (c)))

# endif

# define CANARI_SZ(b)           SUM_CAN(SUM_SZ(b), _can_sz)
# define CANARI_FREE(b)         SUM_CAN(SUM_FREE(b), _can_free)

# define UPDATE_CANARI_SZ(b)    (b)->can_sz   = CANARI_SZ(b)
# define UPDATE_CANARI_FREE(b)  (b)->can_free = CANARI_FREE(b)

# define UPDATE_CANARI_GENE(b)  UPDATE_CANARI_SZ(b); \
                                    if (IS_FREE(b)) { UPDATE_CANARI_FREE(b); }

# define UPDATE_CANARI_BOTH(b)  UPDATE_CANARI_SZ(b); \
                                    UPDATE_CANARI_FREE(b)

# define BAD_CANARI_SZ(b)       ((b)->can_sz != CANARI_SZ(b))
# define BAD_CANARI_FREE(b)     ((b)->can_free != CANARI_FREE(b))

# define BAD_CANARI(b)          (BAD_CANARI_SZ(b) || \
                                    (IS_FREE(b) && BAD_CANARI_FREE(b)))

#endif



/* Bock 0 management */

#define NB_FREE()               b_0->prv_sz /* For random allocation and checking integrity */

#define SZ_FREE()               b_0->sz     /* For checking available free memory */

# define INCREASE_NB_FREE()     b_0->prv_sz = (u__sz_t) (NB_FREE() + 1)
# define DECREASE_NB_FREE()     b_0->prv_sz = (u__sz_t) (NB_FREE() - 1)

# define INCREASE_SZ_FREE(l)    SZ_FREE() = (u__sz_t)(SZ_FREE() + (l))
# define DECREASE_SZ_FREE(l)    SZ_FREE() = (u__sz_t)(SZ_FREE() - (l))

#if CANARIS_INTEGRITY == 1

# define INC_NB_SZ_FREE(l)      INCREASE_SZ_FREE(l); \
                                    INCREASE_NB_FREE(); \
                                    UPDATE_CANARI_SZ(b_0)

#else

# define INC_NB_SZ_FREE(l)      INCREASE_SZ_FREE(l); \
                                    INCREASE_NB_FREE()

#endif


#endif
#endif

