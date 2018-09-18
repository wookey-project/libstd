#ifndef M4_SYNC_H
#define M4_SYNC_H

#include "types.h"

bool core_semaphore_trylock(volatile uint32_t* semaphore);

bool core_semaphore_release(volatile uint32_t* semaphore);

#endif
