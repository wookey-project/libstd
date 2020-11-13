#ifndef __SYNC_H_
#define __SYNC_H_

#include "libc/types.h"
#ifndef __FRAMAC__

/* INFO:
 * backend membarrier asm inline is not executed in FramaC context, because asm inline
 * generates uncontroled peace of code that makes proof problem (assigns are no more
 * validated as asm inline can't be evaluated).
 * As this peace of code is very small (calling dmb instructions) we consider, using a
 * manual review, that there is **no** border effect generating potential RTE or invalid
 * assignation there.
 */

#ifdef CONFIG_ARCH_ARMV7M
# include "libc/arch/cores/armv7-m/m4_sync.h"
#else
# error "unsupported arch backend for memory barrier API"
#endif

#endif

/*
 * These functions permits to ensure that target data are written back in memory before
 * the next instruction happens. This avoid optimization side-effects (typically register
 * caching) when concurrent threads share a given variable.
 *
 * CAUTION: these functions permits to ensure that the given variables (scalar, atomically written
 * in memory (reduced to 32bit scalar types and smaller ones) are correctly pushed back in memory
 * in order to be consistent in the case of a separately threaded (concurrent) accessor.
 *
 * These functions DOES NOT protect consistency for non-atomic types (structures or any type that
 * are *not* atomically written in the corresponding hardware datasheet.
 * To resolve this problematic, please use mutexes and semaphores. In the same way, mutexes and
 * semaphore *does not* protect against compiler optimization and memory barriers myst be used
 * in addition.
 */

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline void set_u8_with_membarrier(uint8_t *target, uint8_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_membarrier();
#endif
}

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline void set_u16_with_membarrier(uint16_t *target, uint16_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_membarrier();
#endif
}

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline void set_u32_with_membarrier(uint32_t *target, uint32_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_membarrier();
#endif
}

/*@
	@ requires \valid(target);
	@ assigns *target ;
	@ ensures *target == val ;
*/
inline void set_bool_with_membarrier(bool *target, bool val) {
    /* let the effective assignation be compiled here */
    *target = val;
#ifndef __FRAMAC__
    arch_data_membarrier();
#endif
}

/*@
  @ assigns \nothing;
*/
inline void request_data_membarrier(void) {
#ifndef __FRAMAC__
    arch_data_membarrier();
#endif
}

#endif/*__SYNC_H_*/
