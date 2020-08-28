#ifndef __ARMV7M_SYNC_H_
#define __ARMV7M_SYNC_H_


/* These functions are helpers for variable assignation that requires
 * memory sync'ed in order to be retreived by any other concurrent thread
 * (typically an interrupt). This is to be done for global variables in order
 * to avoid the volatile keyword, which generates a lot of other side effects */

/*
 * Make sure that any explicit data memory transfer specified before is done before the
 * next data memory transfer.
 */

/*@
	assigns \nothing ;
*/
inline void arch_data_membarrier(void) {
    asm volatile ("dmb");
}


/*
 * Make sure that any explicit data memory transfer specified before is done before the
 * next instruction (harder than previous case, but slower).
 */

/*@
	assigns \nothing ;
*/
inline void arch_data_memsync(void) {
    asm volatile ("dmb");
}


#endif/*__ARMV7M_SYNC_H_*/
