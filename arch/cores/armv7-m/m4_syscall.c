#include "libc/syscall.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "stream/stream_priv.h"
#include "arch/cores/armv7-m/m4_syscall.h"

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

__IN_SEC_VDSO void do_starttask(uint32_t slot, uint32_t seed)
{
    __stack_chk_guard = seed;

    init_ring_buffer();

    /* Initialize the stack protector for all other task's functions */
    _main(slot);

    /* End of task */
    printf("\033[37;43mEnd of task\033[37;40m\n");
    asm volatile ("svc %0\n"::"i" (SVC_EXIT):);

    while (1) {
    };
}

/*
 * This function handles stack check error, corresponding to canary corruption
 * detection
 */
__IN_SEC_VDSO void __stack_chk_fail(void)
{
    /* We have failed to check our stack canary */
    printf("Failed to check the stack guard ! Stack corruption !");

    /* End of task. NOTE: stack corruption is a serious security issue */
    asm volatile ("svc %0\n"::"i" (SVC_EXIT):);

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
__IN_SEC_VDSO void do_startisr(handler_t handler, uint8_t irq, uint32_t status, uint32_t data)
{
    if (handler) {
        handler(irq, status, data);
    }

    /* End of ISR */
    asm volatile ("svc %0\n"::"i" (SVC_EXIT):);

    while (1) {
    };
}

/**
 ** \private
 ** the argument is used for stack access by kernel
 ** This is the arch-specific implementation of the user to supervisor switch
 */
__IN_SEC_VDSO e_syscall_ret do_syscall(e_svc_type svc, __attribute__ ((unused))
                         struct gen_syscall_args *args)
{
    e_syscall_ret ret;

    switch (svc) {
        case SVC_EXIT:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_EXIT),[args] "g"(args)
                          :"r0");
            return ret; /* Is never executed */
        case SVC_YIELD:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_YIELD),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_GET_TIME:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_GET_TIME),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_RESET:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_RESET),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_SLEEP:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_SLEEP),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_GET_RANDOM:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_GET_RANDOM),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_LOG:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_LOG),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_REGISTER_DEVICE:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_REGISTER_DEVICE),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_REGISTER_DMA:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_REGISTER_DMA),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_REGISTER_DMA_SHM:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_REGISTER_DMA_SHM),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_GET_TASKID:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_GET_TASKID),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_INIT_DONE:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_INIT_DONE),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_IPC_RECV_SYNC:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_IPC_RECV_SYNC),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_IPC_SEND_SYNC:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_IPC_SEND_SYNC),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_IPC_RECV_ASYNC:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_IPC_RECV_ASYNC),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_IPC_SEND_ASYNC:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_IPC_SEND_ASYNC),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_GPIO_SET:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_GPIO_SET),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_GPIO_GET:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_GPIO_GET),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_GPIO_UNLOCK_EXTI:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_GPIO_UNLOCK_EXTI),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_DMA_RECONF:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_DMA_RECONF),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_DMA_RELOAD:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_DMA_RELOAD),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_DMA_DISABLE:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_DMA_DISABLE),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_DEV_MAP:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_DEV_MAP),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_DEV_UNMAP:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_DEV_UNMAP),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_DEV_RELEASE:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_DEV_RELEASE),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_LOCK_ENTER:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_LOCK_ENTER),[args] "g"(args)
                          :"r0");
            return ret;
        case SVC_LOCK_EXIT:
            asm volatile ("mov r0, %[args]; svc %[svc]; str  r0, %[ret]\n"
                          :[ret] "=m"(ret)
                          :[svc] "i"(SVC_LOCK_EXIT),[args] "g"(args)
                          :"r0");
            return ret;
        default:
            return SYS_E_INVAL;
    }
}
