#include "libc/syscall.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "stream/stream_priv.h"

/* Global variable holding the stack canary value */
volatile uint32_t __stack_chk_guard = 0;

/**
 ** \private
 */
typedef void (*handler_t) (uint8_t irq, uint32_t status, uint32_t data);

/**
 ** \private
 ** will be replaced by the task's main function.
 */
int     _main(uint32_t slot);

/**
 ** \private
 ** This is the task's real entry point. This finishes properly the execution with a svc, asking
 ** the kernel to set the task as finished.
 ** this function MUST be the first of this file, to allow the linker to place it at the begining
 ** of the slot
 */

#if __GNUC__
#pragma GCC push_options
#pragma GCC optimize("-fno-stack-protector")
#endif

#if __clang__
#pragma clang optimize off
  /* Well, clang support local stack protection deactivation only since v8 :-/ */
#if __clang_major__ > 7
#pragma clang attribute push(__attribute__((no_stack_protector)), apply_to = do_starttask)
#endif
#endif

void do_starttask(uint32_t slot, uint32_t seed)
{
    __stack_chk_guard = seed;

    init_ring_buffer();

    /* Initialize the stack protector for all other task's functions */
    _main(slot);

    /* End of task */
    printf("\033[37;43mEnd of task\033[37;40m\n");
    asm volatile ("svc #1\n":::);

    while (1) {
    };
}

/*
 * This function handles stack check error, corresponding to canary corruption
 * detection
 */
void __stack_chk_fail(void)
{
    /* We have failed to check our stack canary */
    printf("Failed to check the stack guard ! Stack corruption !");

    /* End of task. NOTE: stack corruption is a serious security issue */
    asm volatile ("svc #1\n":::);

    while (1) {
    };
}

#if __clang__
#pragma clang optimize on
#if __clang_major__ > 7
#pragma clang attribute pop
#endif
#endif

#if __GNUC__
#pragma GCC pop_options
#endif

/**
 ** \private
 ** ISR handler glue. The kernel must set the real handler @ in the
 ** stack frame to make the NVIC reload r0 with its @.
 */
void do_startisr(handler_t handler, uint8_t irq, uint32_t status, uint32_t data)
{
    if (handler) {
        handler(irq, status, data);
    }

    /* End of ISR */
    asm volatile ("svc #2\n":::);

    while (1) {
    };
}

/**
 ** \private
 ** the argument is used for stack access by kernel
 ** This is the arch-specific implementation of the user to supervisor switch
 */
e_syscall_ret do_syscall( __attribute__ ((unused))
                         struct gen_syscall_args *args)
{
    e_syscall_ret ret;

    asm volatile ("svc #0\n" "str  r0, %[ret]\n":[ret] "=m"(ret)
                  ::"r0");

    return ret;
}
