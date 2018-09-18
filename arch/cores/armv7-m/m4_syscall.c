#include "api/syscall.h"
#include "print_priv.h"

/**
** \private
*/
typedef void (*handler_t)(uint8_t irq, uint32_t status, uint32_t data);

/**************** libstd glue, to manage the task execution, not to be exported to user ********/
/**
** \private
** will be replaced by the task's main function.
*/
int _main(uint32_t slot);

/**
** \private
** This is the task's real entry point. This finishes properly the execution with a svc, asking
** the kernel to set the task as finished.
** this function MUST be the first of this file, to allow the linker to place it at the begining
** of the slot
*/
void do_starttask(uint32_t slot)
{
    // init printf buffer
    init_ring_buffer();
    _main(slot);

    /* End of task */
    asm volatile ( "svc #1\n" :::);

    /* give some time to SVC IRQ to rise */
    while(1);
}

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
    asm volatile ( "svc #2\n" :::); 

    /* give some time to SVC IRQ to rise */
    while(1);
}

/**
** \private
** the argument is used for stack access by kernel
** This is the arch-specific implementation of the user to supervisor switch
*/
e_syscall_ret do_syscall(__attribute__((unused)) struct gen_syscall_args *args)
{
  e_syscall_ret ret;

  asm volatile (
        "svc #0\n"
        "str  r0, %[ret]\n"
        : [ret] "=m"(ret));
  return ret;
}

