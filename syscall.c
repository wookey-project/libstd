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
#include "libc/types.h"
#include "libc/syscall.h"
#ifdef CONFIG_ARCH_ARMV7M
#include "arch/cores/armv7-m/m4_syscall.h"
#else
#error "Architecture not yet supported by Libstd Syscall API"
#endif

/* Required for variadic macros, compatible with gcc and llvm/clang */
#define __GNU_SOURCES

#ifdef __clang__
/*** Clang/LLVM builtins ****/
static inline void _memset(void *s, int c, uint32_t n)
{
    char   *bytes = s;

    while (n) {
        *bytes = c;
        bytes++;
        n--;
    }
    return;
}

static inline void _memcpy(void *dest, const void *src, uint32_t n)
{
    char   *d_bytes = dest;
    const char *s_bytes = src;

    while (n) {
        *d_bytes = *s_bytes;
        d_bytes++;
        s_bytes++;
        n--;
    }

    return;
}

void __aeabi_memclr(void *dest, int n)
{
    _memset(dest, 0, n);
}

void __aeabi_memclr4(void *dest, int n)
{
    _memset(dest, 0, n);
}

void __aeabi_memclr8(void *dest, int n)
{
    _memset(dest, 0, n);
}

void __aeabi_memcpy(void *dest, const void *src, uint32_t n)
{
    _memcpy(dest, src, n);
}

void __aeabi_memcpy4(void *dest, const void *src, uint32_t n)
{
    _memcpy(dest, src, n);
}

void __aeabi_memcpy8(void *dest, const void *src, uint32_t n)
{
    _memcpy(dest, src, n);
}

#endif

/*
** Syscalls user interface implementation
*/

e_syscall_ret sys_yield(void)
{
    struct gen_syscall_args args = { 0, 0, 0, 0 };
    return do_syscall(SVC_YIELD, &args);
}

e_syscall_ret sys_lock(uint32_t action)
{
    struct gen_syscall_args args = { 0, 0, 0, 0 };
    switch (action) {
        case LOCK_ENTER:
            return do_syscall(SVC_LOCK_ENTER, &args);
        case LOCK_EXIT:
            return do_syscall(SVC_LOCK_EXIT, &args);
        default:
            return SYS_E_INVAL;
    }
}

e_syscall_ret sys_sleep(uint32_t time, sleep_mode_t mode)
{
    struct gen_syscall_args args = { time, mode, 0, 0 };
    return do_syscall(SVC_SLEEP, &args);
}

e_syscall_ret sys_reset(void)
{
    struct gen_syscall_args args = { 0, 0, 0, 0 };
    return do_syscall(SVC_RESET, &args);
}

e_syscall_ret sys_get_systick(uint64_t * val, e_tick_type type)
{
    struct gen_syscall_args args = { (uint32_t) val, type, 0, 0 };
    return do_syscall(SVC_GET_TIME, &args);
}

e_syscall_ret sys_get_random(char *val, uint16_t len)
{
    struct gen_syscall_args args = { (uint32_t) val, (uint32_t) len, 0, 0 };
    return do_syscall(SVC_GET_RANDOM, &args);
}

e_syscall_ret sys_log(logsize_t size, const char *msg)
{
    struct gen_syscall_args args = { (uint32_t) size, (uint32_t) msg, 0, 0 };
    return do_syscall(SVC_LOG, &args);
}

/*************************************************
 * sys_ipc functions
 ************************************************/

e_syscall_ret sys_ipc_IPC_SEND_SYNC( __attribute__ ((unused)) uint32_t ipctype,
                                    uint8_t receiver, logsize_t size,
                                    const char *msg)
{
    struct gen_syscall_args args =
        { (uint32_t) receiver, (uint32_t) size, (uint32_t) msg, 0 };
    return do_syscall(SVC_IPC_SEND_SYNC, &args);
}

e_syscall_ret sys_ipc_IPC_RECV_SYNC( __attribute__ ((unused)) uint32_t ipctype,
                                    uint8_t * sender, logsize_t * size,
                                    char *msg)
{
    struct gen_syscall_args args =
        { (uint32_t) sender, (uint32_t) size, (uint32_t) msg, 0 };
    return do_syscall(SVC_IPC_RECV_SYNC, &args);
}

e_syscall_ret sys_ipc_IPC_SEND_ASYNC( __attribute__ ((unused)) uint32_t ipctype,
                                     uint8_t receiver, logsize_t size,
                                     const char *msg)
{
    struct gen_syscall_args args =
        { (uint32_t) receiver, (uint32_t) size, (uint32_t) msg, 0 };
    return do_syscall(SVC_IPC_SEND_ASYNC, &args);
}


e_syscall_ret sys_ipc_IPC_RECV_ASYNC( __attribute__ ((unused)) uint32_t ipctype,
                                     uint8_t * sender, logsize_t * size,
                                     char *msg)
{
    struct gen_syscall_args args =
        { (uint32_t) sender, (uint32_t) size, (uint32_t) msg, 0 };
    return do_syscall(SVC_IPC_RECV_ASYNC, &args);
}

/*************************************************
 * sys_cfg functions
 ************************************************/

e_syscall_ret sys_cfg_CFG_GPIO_SET( __attribute__ ((unused)) uint32_t cfgtype,
                                   uint8_t gpioref, uint8_t value)
{
    struct gen_syscall_args args = { gpioref, value, 0, 0 };
    return do_syscall(SVC_GPIO_SET, &args);
}

e_syscall_ret sys_cfg_CFG_GPIO_GET( __attribute__ ((unused)) uint32_t cfgtype,
                                   uint8_t gpioref, uint8_t * value)
{
    struct gen_syscall_args args = { gpioref, (uint32_t) value, 0, 0 };
    return do_syscall(SVC_GPIO_GET, &args);
}

e_syscall_ret sys_cfg_CFG_GPIO_UNLOCK_EXTI( __attribute__ ((unused)) uint32_t
                                           cfgtype, uint8_t gpioref)
{
    struct gen_syscall_args args = { gpioref, 0, 0, 0 };
    return do_syscall(SVC_GPIO_UNLOCK_EXTI, &args);
}

e_syscall_ret sys_cfg_CFG_DMA_RECONF( __attribute__ ((unused)) uint32_t cfgtype,
                                     dma_t * dma, dma_reconf_mask_t mask,
                                     int descriptor)
{
    struct gen_syscall_args args =
        { (uint32_t) dma, (uint32_t) mask, (uint32_t) descriptor, 0 };
    return do_syscall(SVC_DMA_RECONF, &args);
}

e_syscall_ret sys_cfg_CFG_DMA_RELOAD( __attribute__ ((unused)) uint32_t cfgtype,
                                     int descriptor)
{
    struct gen_syscall_args args = { (uint32_t) descriptor, 0, 0, 0 };
    return do_syscall(SVC_DMA_RELOAD, &args);
}

e_syscall_ret sys_cfg_CFG_DMA_DISABLE( __attribute__ ((unused)) uint32_t
                                      cfgtype, int descriptor)
{
    struct gen_syscall_args args = { (uint32_t) descriptor, 0, 0, 0 };
    return do_syscall(SVC_DMA_DISABLE, &args);
}

e_syscall_ret sys_cfg_CFG_DEV_MAP( __attribute__ ((unused)) uint32_t cfgtype,
                                  uint32_t devid)
{
    struct gen_syscall_args args = { devid, 0, 0, 0 };
    return do_syscall(SVC_DEV_MAP, &args);
}

e_syscall_ret sys_cfg_CFG_DEV_UNMAP( __attribute__ ((unused)) uint32_t cfgtype,
                                    uint32_t devid)
{
    struct gen_syscall_args args = { devid, 0, 0, 0 };
    return do_syscall(SVC_DEV_UNMAP, &args);
}


e_syscall_ret sys_cfg_CFG_DEV_RELEASE( __attribute__ ((unused)) uint32_t
                                      cfgtype, uint32_t devid)
{
    struct gen_syscall_args args = { devid, 0, 0, 0 };
    return do_syscall(SVC_DEV_RELEASE, &args);
}



/*************************************************
 * sys_init functions
 ************************************************/

e_syscall_ret sys_init_INIT_DEVACCESS( __attribute__ ((unused)) uint32_t
                                      inittype, const device_t * device,
                                      int *descriptor)
{
    struct gen_syscall_args args =
        { (uint32_t) device, (uint32_t) descriptor, 0, 0 };
    return do_syscall(SVC_REGISTER_DEVICE, &args);
}

e_syscall_ret sys_init_INIT_DMA( __attribute__ ((unused)) uint32_t inittype,
                                volatile dma_t * dma, int *descriptor)
{
    struct gen_syscall_args args =
        { (uint32_t) dma, (uint32_t) descriptor, 0, 0 };
    return do_syscall(SVC_REGISTER_DMA, &args);
}

e_syscall_ret sys_init_INIT_DMA_SHM( __attribute__ ((unused)) uint32_t inittype,
                                    dma_shm_t * dmashm)
{
    struct gen_syscall_args args = { (uint32_t) dmashm, 0, 0, 0 };
    return do_syscall(SVC_REGISTER_DMA_SHM, &args);
}

e_syscall_ret sys_init_INIT_GETTASKID( __attribute__ ((unused)) uint32_t
                                      inittype, char *name, uint8_t * id)
{
    struct gen_syscall_args args = { (uint32_t) name, (uint32_t) id, 0, 0 };
    return do_syscall(SVC_GET_TASKID, &args);
}

e_syscall_ret sys_init_INIT_DONE( __attribute__ ((unused)) uint32_t inittype)
{
    struct gen_syscall_args args = { 0, 0, 0, 0 };
    return do_syscall(SVC_INIT_DONE, &args);
}
