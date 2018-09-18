#ifndef M4_SYSCALL_H_
#define M4_SYSCALL_H_

#include "api/types.h"
#include "kernel/exported/syscalls.h"

/**
** \private
*/
e_syscall_ret do_syscall(__attribute__((unused)) struct gen_syscall_args *args);

e_syscall_ret do_fastcall(__attribute__((unused)) struct gen_syscall_args *args);

#endif /*!SYSCALL_H_*/
