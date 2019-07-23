#ifndef M4_SYSCALL_H_
#define M4_SYSCALL_H_

#include "libc/types.h"
#include "kernel/src/C/exported/syscalls.h"

/* This macros permits to add some specific functions to a section named
 * '.vdso'. In small MPU based system (based on 8 regions), it is useless,
 * but on bigger systems (MPU with 16 regions, MMU-based systems), this part
 * of the libc can be mapped in a separated part of the task memory layout
 * in order to allow the kernel to check that any syscall entrypoint is
 * called through the VDSO only, to ensure that userspace supplementary checks
 * are done.
 * REQ: the syscalls userspace glue must be built as single functions to
 * avoid any direct call to the arch-specific kernel call of the VDSO.
 *
 * Why hosting VDSO in the libstd instead of the kernel ?
 * Just because in small MPU based system, there is no memory region to map
 * a dedicated section for the .vdso content, and as a consequence this section
 * as to be mapped in the same region as the overall userspace text content.
 * Remember: there is no memory abstraction in MPU-based systems.
 */
#define __IN_SEC_VDSO __attribute__((section(".vdso")))

/**
** \private
*/
e_syscall_ret do_syscall(e_svc_type svc,  __attribute__ ((unused)) struct gen_syscall_args * args);

#endif /*!SYSCALL_H_ */
