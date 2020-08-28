#ifndef __SYNC_H_
#define __SYNC_H_

#include "libc/types.h"
#ifdef CONFIG_ARCH_ARMV7M
# include "libc/arch/cores/armv7-m/m4_sync.h"
#else
# error "unsupported arch backend for memory barrier API"
#endif

/*
 * TODO: is arch_data_membarrier() not enough here ? instead of memsync.
 */

inline void set_u8_with_memsync(uint8_t *target, uint8_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
    arch_data_memsync();
}

inline void set_u16_with_memsync(uint16_t *target, uint16_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
    arch_data_memsync();
}

inline void set_u32_with_memsync(uint32_t *target, uint32_t val) {
    /* let the effective assignation be compiled here */
    *target = val;
    arch_data_memsync();
}

#endif/*__SYNC_H_*/
