#ifndef SEMAPHORE_H_
#define SEMAPHORE_H_

void semaphore_init(uint8_t value, volatile uint32_t* semaphore);

bool semaphore_trylock(volatile uint32_t* semaphore);

bool semaphore_release(volatile uint32_t* semaphore);

#endif
