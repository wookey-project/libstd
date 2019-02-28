#ifndef SEMAPHORE_H_
#define SEMAPHORE_H_

/* semaphore, with potential concurrent access allowed */
void semaphore_init(uint8_t value, volatile uint32_t* semaphore);

bool semaphore_trylock(volatile uint32_t* semaphore);

void semaphore_lock(volatile uint32_t* semaphore);

bool semaphore_release(volatile uint32_t* semaphore);

/* effective mutex (Mutual Exclusion) */
void mutex_init(volatile uint32_t* mutex);

bool mutex_trylock(volatile uint32_t* mutex);

void mutex_lock(volatile uint32_t* mutex);

void mutex_unlock(volatile uint32_t* mutex);

#endif
