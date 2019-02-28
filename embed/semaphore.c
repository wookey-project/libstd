#include "api/types.h"
#include "autoconf.h"
#ifdef CONFIG_ARCH_ARMV7M
#include "arch/cores/armv7-m/m4-sync.h"
#else
#error "Unknown architecture"
#endif
#include "semaphore.h"

/*
 * The semaphore is initialized with 'value'.
 * value determine the number of concurrent threads that can access
 * a ressource in the same time.
 * If value is 1, this semaphore is a mutex
 */
void semaphore_init(uint8_t value, volatile uint32_t *semaphore)
{
    *semaphore = value;
}

/*
 * Try to lock the current semaphore
 */
bool semaphore_trylock(volatile uint32_t* semaphore)
{
    return core_semaphore_trylock(semaphore);
}

void semaphore_lock(volatile uint32_t* semaphore)
{
    bool is_locked = false;
    do {
        is_locked = core_semaphore_trylock(semaphore);
    } while (!is_locked);
}



bool semaphore_release(volatile uint32_t* semaphore)
{
    return core_semaphore_release(semaphore);
}
