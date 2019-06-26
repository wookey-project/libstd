/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef SYSCALL_H
#define SYSCALL_H

#include "autoconf.h"
#include "libc/interrupt.h"
#include "libc/types.h"
#include "kernel/src/C/exported/syscalls.h"
#include "kernel/src/C/exported/devices.h"
#include "kernel/src/C/exported/dmas.h"
#include "kernel/src/C/exported/sleep.h"

// FIXME - nothing to do here!
#ifdef CONFIG_STM32F4
typedef enum {
    AHB1 = 0,
    AHB2,
    APB1,
    APB2
} e_soc_bus_ref;
#else
#error "buses unknown for current architecture"
#endif

/** @private */
struct gen_syscall_args {
    uint32_t reg0;
    uint32_t reg1;
    uint32_t reg2;
    uint32_t reg3;
};

/**
 * \private
 * Effective syscall prototypes. This functions should not be called
 * directly but only through the syscall handling variadic macros.
 * These macros permits:
 * - to support variadic syscall prototypes for easy usage (without
 *   requiring explicit casting or fixed args number when not needed)
 * - to keep a complete type checking at compile time, the macro
 *   being replaced by the corresponding function at preprocessing time
 * \{
 */
e_syscall_ret sys_init_INIT_DEVACCESS(uint32_t inittype, const device_t *device, int *descriptor);
e_syscall_ret sys_init_INIT_DMA(uint32_t inittype, volatile dma_t *dma, int *descriptor);
e_syscall_ret sys_init_INIT_DMA_SHM(uint32_t inittype, dma_shm_t *dmashm);
e_syscall_ret sys_init_INIT_GETTASKID(uint32_t inittype, char *name, uint8_t *id);
e_syscall_ret sys_init_INIT_DONE(uint32_t inittype);


e_syscall_ret sys_cfg_CFG_GPIO_SET(uint32_t cfgtype, uint8_t gpioref, uint8_t value);
e_syscall_ret sys_cfg_CFG_GPIO_GET(uint32_t cfgtype, uint8_t gpioref, uint8_t *value);
e_syscall_ret sys_cfg_CFG_GPIO_UNLOCK_EXTI(uint32_t cfgtype, uint8_t gpioref);
e_syscall_ret sys_cfg_CFG_DMA_RECONF(uint32_t cfgtype, dma_t*dma, dma_reconf_mask_t mask, int descriptor);
e_syscall_ret sys_cfg_CFG_DMA_RELOAD(uint32_t cfgtype, int descriptor);
e_syscall_ret sys_cfg_CFG_DMA_DISABLE(uint32_t cfgtype, int descriptor);
e_syscall_ret sys_cfg_CFG_DEV_MAP(uint32_t cfgtype, uint32_t devid);
e_syscall_ret sys_cfg_CFG_DEV_UNMAP(uint32_t cfgtype, uint32_t devid);
e_syscall_ret sys_cfg_CFG_DEV_RELEASE(uint32_t cfgtype, uint32_t devid);

e_syscall_ret sys_ipc_IPC_SEND_SYNC(uint32_t ipctype, uint8_t receiver, logsize_t size, const char *msg);
e_syscall_ret sys_ipc_IPC_RECV_SYNC(uint32_t ipctype, uint8_t *sender, logsize_t *size, char *msg);
e_syscall_ret sys_ipc_IPC_SEND_ASYNC(uint32_t ipctype, uint8_t receiver, logsize_t size, const char *msg);
e_syscall_ret sys_ipc_IPC_RECV_ASYNC(uint32_t ipctype, uint8_t *sender, logsize_t *size, char *msg);

e_syscall_ret sys_log (logsize_t size, const char *msg);

/**
 * \}
 */


/**
** \brief set the task as idle
**
** The task is no more schedulable, but will be awoken by an external IPC or any of its ISR being executed.
** It permits to support a blocking wait() function with ISR or IPC receive condition.
**
** The wakening condition determination is up to the task (reading a variable set by all its ISR, do a
** sys_ipc(IPC_RECV_ASYNC), etc.)
**
** This syscall results in the immediate scheduling of another task without violation of the scheduling scheme.
*/
e_syscall_ret sys_yield(void);

/**
** \brief ask for urgent board reset
**
** The task requests an immediate board software reset. This will clean any secret information or data into
** the board RAM or IPs, avoiding any future use of it. This syscall request the PERM_RES_TSK_RST permission.
**
*/
e_syscall_ret sys_reset(void);

e_syscall_ret sys_sleep(uint32_t time, sleep_mode_t mode);

e_syscall_ret sys_lock(uint32_t action);

/**
** \brief The global inter-process communication system
**
** There is two distinguished target for the IPC:
**
** ### a userspace task (target_task = target slot)
**   the ipctype can be one of:
**
**   - IPC_SEND_SYNC
**
**     prototype: sys_ipc(<target>, IPC_SEND_SYNC, <size>, <msg>);
**
**     Send a message to <target>. If the <target> input buffer is free, the message is written and
**     the current task is set as TSK_SVC_LOCKED while the target has not read the message.
**
**     The task is set as runable when the target as read the message from its local IPC buffer.
**     If used before init sequence of the task is finished, the syscall do nothing but returns
**     SYS_E_DENIED.
**
**     Beware, this IPC may result in deadlocks between tasks !
**
**     \include examples/syscalls/ipc_send_sync.c
**
**   - IPC_RECV_SYNC
**
**     prototype: sys_ipc(<target>, IPC_RECV_SYNC, <size>, <msg>);
**
**     Read from local IPC buffer into msg up to size (or IPC buffer size) and update <size> with
**     the size read. Input IPC buffer is ready to receive another IPC if needed and the sender
**     of the current message is runnable again.
**
**     If there is no message to read, the task is set as
**     TSK_SVC_LOCKED until someone send it an IPC msg. If used before init sequence of the task is
**     finished, the syscall do nothing but returns SYS_E_DENIED.
**
**     \include examples/syscalls/ipc_recv_sync.c
**
**   - IPC_SEND_ASYNC
**
**     prototype: sys_ipc(<target>, IPC_SEND_ASYNC, <size>, <msg>);
**
**     Send the message to <target>. If <target> input buffer is free the message is written and
**     the syscall return SYS_E_DONE, otherwise the syscall returns SYS_E_BUSY.
**
**     If used before init sequence of the task is finished, the syscall do nothing but returns
**     SYS_E_DENIED.
**
**     \include examples/syscalls/ipc_send_sync.c
**
**   - IPC_RECV_ASYNC
**
**     prototype: sys_ipc(<target>, IPC_RECV_ASYNC, <size>, <msg>);
**
**     Read from the local IPC buffer, up to size of IPC buffer size, and update <size> with the
**     size read. IPC buffer size is ready to receive again and the sender of the current message
**     is runnable again (if needed).
**
**     If there is no message to read, the syscall returns
**     SYS_E_INVAL, otherwise it returns SYS_E_DONE. If used before init sequence of the task is
**     finished, the syscall do nothing but returns SYS_E_DENIED.
**
**     \include examples/syscalls/ipc_recv_async.c
**
*/
#define sys_ipc(cmd,...) \
    sys_ipc_ ## cmd (cmd, ## __VA_ARGS__)

/**
** \brief The global poist-initialization configuration system call
**
** This function permit to reconfigure devices that permit dynamic reconfiguration at
** runtime, such as GPIOs or DMA controllers.
**
** There is two main configuration familly: GPIO configuration, that permit to interact with
** GPIOs, and DMA configuration, that permit to reset, reconfigure and reload DMA streams.
**
** For all devices, the declaration must be done in the init phase. This function does not
** permit post-init device declaration.
**
** ### GPIO configuration
**
**   - CFG_GPIO_SET
**
**     prototype: sys_cfg(CFG_GPIO_SET, uint8_t gpioref, uint8_t value);
**
**     Set the value 'value' to the gpio specified by gpioref. gpioref respect the following:
**     gpioref = port << 4 + pin
**
**     The kernel will check that the GPIO has been previously registered and enabled by this task
**     otherwise it will return SYS_E_INVAL.
**
**   - CFG_GPIO_GET
**
**     prototype: sys_cfg(CFG_GPIO_GET, uint8_t gpioref, uint8_t *val);
**
**     Get back the value of gpioref into val. If the GPIO has been previously registered and
**     enabled by this task, the value is returned in val, otherwise it will return SYS_E_INVAL.
**
** ### DMA configuration
**
**   - CFG_DMA_RELOAD
**
**     prototype: sys_cfg(CFG_DMA_RELOAD, int descriptor);
**
**     Start the DMA stream (rise the corresponding enable bit to 1) if the corresponding dma_t
**     structure previously registered in the kernel has been fullfilled.
**
**     This permit to reload the DMA when looping on DMA transfers without modifying the DMA
**     configuration. The dma_id value is the value given by the kernel at DMA declaration time
**     during the init phase in the id field of the dma_t structure. This is a value identifying
**     the DMA stream for the kernel, which permit to associate it to an existing, previously
**     registered dma_t structure.
**
**   - CFG_DMA_RECONF
**
**     prototype: sys_cfg(CFG_DMA_RECONF, dma_t*dma, dma_reconf_mask_t reconfmask, int descriptor);
**
**     Reconfigure some part of the DMA controller structure. Only the fields supported in the
**     reconfiguration mask can be reconfigured after the end of init.
**
**     If all the informations needed to start the DMA are set, this function enable the DMA
**     controller, otherwhise, the kernel wait for another call to CFG_DMA_RECONF. This permit
**     the userspace to configure any DMA streams in multiple times, the DMA being started only
**     when all the informations are correctly set.
**
**     Using this function is not required if all informations are set during the initialization
**     phase, when the DMA stream has been declared. In that case, only a call to CFG_DMA_RELOAD
**     is enough, after the end of init, to start the DMA.
**
**   - CFG_DMA_DISABLE
**
**     prototype: sys_cfg(CFG_DMA_DISABLE, int descriptor);
**
**     Disable the given DMA stream. This function temprarilly disable a DMA stream action
**     by deactivating the corresponding enable bit. This action is reversible using one
**     of CFG_DMA_RECONF or CFG_DMA_RELOAD actions.
**
*/
#define sys_cfg(cmd,...) \
    sys_cfg_ ## cmd (cmd, ## __VA_ARGS__)

/**
** \brief set a 32bits unsigned value with the current systick
*/
e_syscall_ret sys_get_systick(uint64_t * val,  e_tick_type type);

/**
 * \brief return random content of len size
 * On Ada kernel, len must not be greater than 16 bytes.
 */
e_syscall_ret sys_get_random(char * val, uint16_t len);

/**
** \brief task initialization function, to declare devices and finalize init step.
**
** ### Synopsis
**
** This syscall is used in order to:
**   - Declare devices
**
**   - Set initialization step as done and activate all devices
**
** Setting initialization step as done is a *requirement* in order to activate registered devices,
** and GPIOs, but also to communicate with other tasks. Otherwise, devices will stay deactivated
** (with no RCC clock entry configured) and the task will not be able to communicate with others
** using sys_ipc syscall (SYS_E_DENIED will be returned).
**
** ### Using sys_init
**
** sys_init supports four subtypes:
**
**   - INIT_DEVACCESS
**
**   prototype: sys_init(INIT_DEVACCESS, device_t*dev);
**
**   Register the devices specified by the device_t struct pointed by dev. The device_t struct is
**   described in kernel/exported/device.h.
**
**   A device have 0 up to 4 GPIOs, 0 up to 8 IRQ lines. for each configure dev->gpios[] and
**   dev->irqs[] accordingly, and set the number of gpios and irqs in dev->num_gpios and
**   dev->num_irqs.
**
**   A device should have a name, (const char[16]), for pretty-printing. The kernel will not
**   rename the device and its name will be an empty string.
**
**   After the usual user content sanitation, the kernel check multiple elements of the device_t
**   struct:
**      - each IRQ line must be free to use (not already registered by someone else) and using
**        a valid IRQ value (in a range allowed by the kenrel, you can't register the memory
**        fault handler)
**      - each GPIO must exist in the target SoC and be free to use (not already registered by
**        someone else
**      - the device must exist in the SoC, its base address and size should correspond to the SoC
**        device map and its bus to the corresponding SoC bus.
**      - the device must not be already registered by someone else
**      - you must not register more than MAX_DEVICES (in ARM Cortex-M MPU MAX_DEVICES is 2)
**      - the task must not have already finished its initialization step
**
**  For more information about how to set GPIO and IRQ content of the device, look at the See Also
**  section.
**  \sa device_t, dev_gpio_info_t, dev_irq_info_t
**
**  \include examples/syscalls/sys_init_devaccess.c
**
**   - INIT_DMA
**
**   prototype: sys_init(INIT_DMA, dma_t*dma, int *descriptor);
**
**  Configure a DMA stream. The handler is awoken by the DMA ontroller when
**  the memory copy is finished.
**
**  The userspace DMA driver has only access to the DMA stream CR register.
**  Other registers, and particulary address registers can't be acceded
**  directly to avoid any security risks by using DMA for incontrolled memory
**  copy.
**  The status register of the stream is not accessible but its value is
**  passed to the ISR as second argument by the kernel.
**
**  Like all other declared user ISR, the user function is then executed in user thread mode, within
**  the task context and with the task access rights. the user ISR has its own stack but has an access
**  to the task's globals and functions if needed. The ISR can't be preempted by another task but can
**  be preempted by physical interrupts, its behavior corresponding to a bottom-half handler.
**
**  \include examples/syscalls/sys_init_dma.c
**
**  For more information about how to configure DMA streams in userspace, look at the See Also
**  section.
**
**   \sa dma_t
**
**   - INIT_DMA_SHM
**
**   prototype: sys_init(INIT_DMA_SHM, dma_shm_t* dma_shm);
**
**  Configure a DMA shared memory with another task. This permit another task to initiate a DMA trasfer
**  from or toward the DMA SHM declared here. Such mechanism permit such structuration:
**    task B declare a DMA SHM in its slot, authorizing task A to initiate DMA toward it
**    task A which to receive data (in DMA) from a given device (e.g. USB HS)
**    task A can directly transfer it to task B. Task A still manage the source device and associated driver
**    when the transfer is finished,task A send an IPC to task B to inform it that the data are ready
**    task B can initiate another DMA transfer, for e.g. toward another device (CRYP, SDIO...)
**
**    A more efficient way is to use a pipeline between task A and task B, allowing parallel DMA transfers,
**    which is possible using the very same API
**
**  For more information about how to configure DMA streams in userspace, look at the See Also
**  section.
**
**   \sa dma_t dma_shm_t
**
**   - INIT_GETTASKID
**
**  prototype: sys_init(INIT_DEVACCESS, char*name, uint32_t*id);
**
**  Get back a given task identifier, using its name.
**
**  This is this only way to get back the identifier of a task you which to communicate with.
**  the name must be exactly the same as the other task's name.
**
**  If the other task is found, id is updated with the target task identifier. This identifier can be
**  used for IPCs. kernel identifier is always 0. You don't need to request kernel id. Requesting the
**  kernel identifier will always return SYS_E_INVAL.
**
**  If the name is not found, the kernel will return SYS_E_INVAL, otherwhise it will returns SYS_E_DONE
**  and id will be udpated.
**
**  this syscall is only allowed during the init phase. After calling sys_init(INIT_DONE, 0, 0), this
**  syscall will always return SYS_E_DENIED.
**
**  \include examples/syscalls/sys_init_gettaskid.c
**
**   - INIT_DONE
**
**   prototype: sys_init(INIT_DONE);
**
**  Finalize the initialization phase:
**   - No more sys_init() syscalls will be allowed
**
**   - IPCs targetting user tasks are now allowed
**
**   - All registered devices and dma streams are activated
**
**  It is possible not to use the sys_init(INIT_DONE) syscall, but the task will
**  have a highly restricted access to the system (no devices, no IPC other than
**  targetting the kernel, etc.).
**
*/
#define sys_init(cmd,...) \
    sys_init_ ## cmd (cmd, ## __VA_ARGS__)

#endif
