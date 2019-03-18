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
#include "api/types.h"
#include "api/syscall.h"
#ifdef CONFIG_ARCH_ARMV7M
#include "arch/cores/armv7-m/m4_syscall.h"
#endif

/* Required for variadic macros, compatible with gcc and llvm/clang */
#define __GNU_SOURCES

#ifdef __clang__
/*** Clang/LLVM builtins ****/
static inline void _memset(void *s, int c, uint32_t n)
{
    char *bytes = s;
    while (n) {
        *bytes = c;
        bytes++;
        n--;
    }
    return;
}

static inline void _memcpy(void *dest, const void *src, uint32_t n)
{
    char *d_bytes = dest;
    const char *s_bytes = src;

    while (n) {
        *d_bytes = *s_bytes;
        d_bytes++;
        s_bytes++;
        n--;
    }

    return;
}

void __aeabi_memclr(void *dest, int n){
        _memset(dest, 0, n);
}

void __aeabi_memclr4(void *dest, int n){
        _memset(dest, 0, n);
}

void __aeabi_memclr8(void *dest, int n){
        _memset(dest, 0, n);
}

void __aeabi_memcpy(void *dest, const void *src, uint32_t n){
	_memcpy(dest, src, n);
}

void __aeabi_memcpy4(void *dest, const void *src, uint32_t n){
	_memcpy(dest, src, n);
}

void __aeabi_memcpy8(void *dest, const void *src, uint32_t n){
	_memcpy(dest, src, n);
}

#endif

/*
** This is the syscall user interface implementation
*/
e_syscall_ret sys_yield(void)
{
    struct gen_syscall_args args = { SYS_YIELD, 0, 0, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_lock(uint32_t action)
{
    struct gen_syscall_args args = { SYS_LOCK, action, 0, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_sleep(uint32_t time, sleep_mode_t mode)
{
    struct gen_syscall_args args = { SYS_SLEEP, time, mode, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}



e_syscall_ret sys_reset(void)
{
    struct gen_syscall_args args = { SYS_RESET, 0, 0, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}



e_syscall_ret sys_get_systick(uint64_t * val, e_tick_type type)
{
    struct gen_syscall_args args = { SYS_GETTICK, (uint32_t) val, type, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_get_random(char * val, uint16_t len)
{
    struct gen_syscall_args args = { SYS_GET_RANDOM, (uint32_t) val, (uint32_t)len, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}


e_syscall_ret sys_log(logsize_t size, const char *msg)
{
    struct gen_syscall_args args = { SYS_LOG, (uint32_t)size, (uint32_t)msg, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

/*************************************************
 * sys_ipc functions
 ************************************************/

/*
 *   prototype: sys_ipc(IPC_SEND_SYNC, uint8_t receiver, logsize_t size, const char *msg);
 *   prototype: sys_ipc(IPC_RECV_SYNC, uint8_t *sender, logsize_t* size, char* msg);
 *   prototype: sys_ipc(IPC_SEND_ASYNC, uint8_t receiver, logsize_t size, const char *msg);
 *   prototype: sys_ipc(IPC_RECV_ASYNC, uint8_t *sender, logsize_t* size, char* msg);
 */

e_syscall_ret sys_ipc_IPC_SEND_SYNC(uint32_t ipctype, uint8_t receiver, logsize_t size, const char *msg)
{
    uint32_t lsize = size;
    uint32_t lreceiver = receiver;
    struct gen_syscall_args args =
        { SYS_IPC, ipctype, lreceiver, lsize, (uint32_t)msg };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_ipc_IPC_RECV_SYNC(uint32_t ipctype, uint8_t *sender, logsize_t *size, char *msg)
{
    struct gen_syscall_args args =
        { SYS_IPC, ipctype, (uint32_t)sender, (uint32_t)size, (uint32_t)msg };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_ipc_IPC_SEND_ASYNC(uint32_t ipctype, uint8_t receiver, logsize_t size, const char *msg)
{
    uint32_t lsize = size;
    uint32_t lreceiver = receiver;
    struct gen_syscall_args args =
        { SYS_IPC, ipctype, lreceiver, lsize, (uint32_t)msg };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}


e_syscall_ret sys_ipc_IPC_RECV_ASYNC(uint32_t ipctype, uint8_t *sender, logsize_t *size, char *msg)
{
    struct gen_syscall_args args =
        { SYS_IPC, ipctype, (uint32_t)sender, (uint32_t)size, (uint32_t)msg };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

/*************************************************
 * sys_cfg functions
 ************************************************/

/*
 *
 *   prototype: sys_cfg(CFG_GPIO_SET, uint8_t gpioref, uint8_t value);
 *   prototype: sys_cfg(CFG_GPIO_GET, uint8_t gpioref, uint8_t *val);
 *   prototype: sys_cfg(CFG_GPIO_UNLOCK_EXTI, uint8_t gpioref);
 *   prototype: sys_cfg(CFG_DMA_RECONF, dma_t*dma, dma_reconf_mask_t reconfmask, int descriptor);
 *   prototype: sys_cfg(CFG_DMA_RELOAD, int descriptor);
 *   prototype: sys_cfg(CFG_DMA_DISABLE, int descriptor);
 *   prototype: sys_cfg(CFG_DEV_MAP, uint32_t dev_id);
 *   prototype: sys_cfg(CFG_DEV_UNMAP, uint32_t dev_id);
 */

e_syscall_ret sys_cfg_CFG_GPIO_SET(uint32_t cfgtype, uint8_t gpioref, uint8_t value)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, gpioref, value, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_cfg_CFG_GPIO_GET(uint32_t cfgtype, uint8_t gpioref, uint8_t *value)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, gpioref, (uint32_t)value, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_cfg_CFG_GPIO_UNLOCK_EXTI(uint32_t cfgtype, uint8_t gpioref)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, gpioref, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}


#ifdef CONFIG_KERNEL_DMA_ENABLE
e_syscall_ret sys_cfg_CFG_DMA_RECONF(uint32_t cfgtype, dma_t*dma, dma_reconf_mask_t mask, int descriptor)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, (uint32_t)dma, (uint32_t)mask, (uint32_t)descriptor};
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_cfg_CFG_DMA_RELOAD(uint32_t cfgtype, int descriptor)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, (uint32_t)descriptor, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_cfg_CFG_DMA_DISABLE(uint32_t cfgtype, int descriptor)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, (uint32_t)descriptor, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

#endif
e_syscall_ret sys_cfg_CFG_DEV_MAP(uint32_t cfgtype, uint32_t devid)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, devid, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

e_syscall_ret sys_cfg_CFG_DEV_UNMAP(uint32_t cfgtype, uint32_t devid)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, devid, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}


e_syscall_ret sys_cfg_CFG_DEV_RELEASE(uint32_t cfgtype, uint32_t devid)
{
    struct gen_syscall_args args =
        { SYS_CFG, cfgtype, devid, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}



/*************************************************
 * sys_init functions
 ************************************************/

/*
**   prototype: sys_init(INIT_DEVACCESS, device_t*dev);
**   prototype: sys_init(INIT_DMA, dma_t*dma);
**   prototype: sys_init(INIT_DMA_SHM, dma_shm_t* dma_shm);
**   prototype: sys_init(INIT_GETTASKID, char*name, uint32_t*id);
**   prototype: sys_init(INIT_DONE);
*/

e_syscall_ret sys_init_INIT_DEVACCESS(uint32_t inittype, const device_t *device, int *descriptor)
{
    struct gen_syscall_args args =
        { SYS_INIT, (uint32_t) inittype, (uint32_t) device, (uint32_t) descriptor, 0 };
    e_syscall_ret ret;
    ret = do_syscall(&args);
    return ret;
}

e_syscall_ret sys_init_INIT_DMA(uint32_t inittype, volatile dma_t *dma, int *descriptor)
{
    struct gen_syscall_args args =
        { SYS_INIT, (uint32_t) inittype, (uint32_t) dma, (uint32_t) descriptor, 0 };
    e_syscall_ret ret;
    ret = do_syscall(&args);
    return ret;
}

e_syscall_ret sys_init_INIT_DMA_SHM(uint32_t inittype, dma_shm_t *dmashm)
{
    struct gen_syscall_args args =
        { SYS_INIT, (uint32_t) inittype, (uint32_t) dmashm, 0, 0 };
    e_syscall_ret ret;
    ret = do_syscall(&args);
    return ret;
}

e_syscall_ret sys_init_INIT_GETTASKID(uint32_t inittype, char *name, uint8_t *id)
{
    struct gen_syscall_args args =
        { SYS_INIT, (uint32_t) inittype, (uint32_t) name, (uint32_t) id, 0 };
    e_syscall_ret ret;
    ret = do_syscall(&args);
    return ret;
}

e_syscall_ret sys_init_INIT_DONE(uint32_t inittype)
{
    struct gen_syscall_args args =
        { SYS_INIT, (uint32_t) inittype, 0, 0, 0 };
    e_syscall_ret ret;
    ret = do_syscall(&args);
    return ret;
}

