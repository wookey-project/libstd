#include "api/types.h"
#include "autoconf.h"
#ifdef CONFIG_ARCH_ARMV7M
#include "arch/cores/armv7-m/m4-sync.h"
#else
#error "Unknown architecture"
#endif
#include "semaphore.h"

/*
 * The mutex is initialized with 1 (unlocked).
 * value determine the number of concurrent threads that can access
 * a ressource in the same time.
 */
void mutex_init(volatile uint32_t *mutex)
{
    *mutex = 1;
}

/*
 * Try to lock the current semaphore
 */
bool mutex_trylock(volatile uint32_t* mutex)
{
    return core_semaphore_trylock(mutex);
}

void mutex_lock(volatile uint32_t* mutex)
{
    bool is_locked = false;
    do {
        is_locked = core_semaphore_trylock(mutex);
    } while (!is_locked);
}


void mutex_unlock(volatile uint32_t* mutex)
{
    /* as it is a mutex we unlock, we should be the lonly user of the
     * semaphore varibale. If the application try to access the
     * variable directly (without the mutex directive... we consider
     * that it is its own problem... */
    core_semaphore_release(mutex);
}
