#include "api/types.h"
#include "api/syscall.h"
#ifdef CONFIG_ARCH_ARMV7M
#include "arch/cores/armv7-m/m4_syscall.h"
#endif

/* Required for variadic macros, compatible with gcc and llvm/clang */
#define __GNU_SOURCES

/*
** This is the syscall user interface implementation
*/
e_syscall_ret sys_yield(void)
{
    struct gen_syscall_args args = { SYS_YIELD, 0, 0, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return SYS_E_DONE;
}

e_syscall_ret sys_lock(uint32_t action)
{
    struct gen_syscall_args args = { SYS_LOCK, action, 0, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return SYS_E_DONE;
}

e_syscall_ret sys_sleep(uint32_t time, sleep_mode_t mode)
{
    struct gen_syscall_args args = { SYS_SLEEP, time, mode, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return SYS_E_DONE;
}



e_syscall_ret sys_reset(void)
{
    struct gen_syscall_args args = { SYS_RESET, 0, 0, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return SYS_E_DONE;
}



e_syscall_ret sys_get_systick(uint64_t * val, e_tick_type type)
{
    struct gen_syscall_args args = { SYS_GETTICK, (uint32_t) val, type, 0, 0 };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

/*************************************************
 * sys_ipc functions
 ************************************************/

/*
 *   prototype: sys_ipc(IPC_LOG, logsize_t size, const char *msg);
 *   prototype: sys_ipc(IPC_SEND_SYNC, uint8_t receiver, logsize_t size, const char *msg);
 *   prototype: sys_ipc(IPC_RECV_SYNC, uint8_t *sender, logsize_t* size, char* msg);
 *   prototype: sys_ipc(IPC_SEND_ASYNC, uint8_t receiver, logsize_t size, const char *msg);
 *   prototype: sys_ipc(IPC_RECV_ASYNC, uint8_t *sender, logsize_t* size, char* msg);
 */

e_syscall_ret sys_ipc_IPC_LOG(uint32_t ipctype, logsize_t size, const char *msg)
{
    uint32_t lsize = size;
    /* default target is kernel (target 0), this does not require a user specification */
    struct gen_syscall_args args =
        { SYS_IPC, ipctype, 0, lsize, (uint32_t)msg };
    e_syscall_ret ret;

    ret = do_syscall(&args);

    return ret;
}

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

e_syscall_ret sys_init_INIT_DEVACCESS(uint32_t inittype, device_t *device, int *descriptor)
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

