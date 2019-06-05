#ifndef M4_SYSCALL_H_
#define M4_SYSCALL_H_

#include "libc/types.h"
#include "kernel/src/C/exported/syscalls.h"

/**
** \private
*/
e_syscall_ret do_syscall(e_svc_type svc,  __attribute__ ((unused)) struct gen_syscall_args * args);

#endif /*!SYSCALL_H_ */
