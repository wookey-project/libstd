#ifndef __ARMV7M_SYNC_H_
#define __ARMV7M_SYNC_H_


/* These functions are helpers for variable assignation that requires
 * memory sync'ed in order to be retreived by any other concurrent thread
 * (typically an interrupt). This is to be done for global variables in order
 * to avoid the volatile keyword, which generates a lot of other side effects
 *
 * INFO: As Frama-C is unable to determine the impact of the asm inline content and thus
 * unable to validate neither a precondition nor a full specification, we have deactivate
 * the lonely ASM call the Data Memory Barrier only in the FRAMAC case.
 * This is the consequence of a code review, as DMB does not impact in any case the
 * function weakest precondition.
 * The function contract is so specific that it can't be defined in ACSL as the DMB is
 * not a C language level notion.
 */

/*
 * Make sure that any explicit data memory transfer specified before is done before the
 * next data memory transfer.
 */

/*@
	assigns \nothing ;
*/
inline void arch_data_membarrier(void) {
#ifndef __FRAMAC__
    asm volatile ("dmb");
#endif
}


/*
 * Make sure that any explicit data memory transfer specified before is done before the
 * next instruction (harder than previous case, but slower).
 */

/*@
	assigns \nothing ;
*/
inline void arch_data_memsync(void) {
#ifndef __FRAMAC__
    asm volatile ("dsb");
#endif
}


#endif/*__ARMV7M_SYNC_H_*/
