#include "api/types.h"


bool core_semaphore_trylock(volatile uint32_t* semaphore)
{
    asm volatile goto (
      "ldrex   r1, [%[semaddr]]\n\t"
      "cmp     r1, #0\n\t"        // Test if semaphore holds the value 0
      "beq     %l[fail]\n\t"           // If it does, block before retrying
      "sub     r1, #1\n\t"        // If not, decrement temporary copy
      "strex   r2, r1, [%[semaddr]]\n\t" // Attempt Store-Exclusive
      "cmp     r2, #0\n\t"        // Check if Store-Exclusive succeeded
      "bne     %l[fail]\n\t"          // If Store-Exclusive failed, retry from start
      "dmb"                   // Required before accessing protected resource
         : 
         : [semaddr] "r"(semaphore) // in
         : "r1", "r2"
         : fail);
    return true;
fail:
    return false;
}

bool core_semaphore_release(volatile uint32_t* semaphore)
{
    asm volatile goto (
      "ldrex   r1, [%[semaddr]]\n\t"
      "add     r1, #1\n\t"        // Increment temporary copy
      "strex   r2, r1, [%[semaddr]]\n\t" // Attempt Store-Exclusive
      "cmp     r2, #0\n\t"        // Check if Store-Exclusive succeeded
      "bne     %l[fail]\n\t"          // If Store-Exclusive failed, retry from start
      "dmb"                   // Required before accessing protected resource
         : 
         : [semaddr] "r"(semaphore) // in
         : "r1", "r2"
         : fail);
    return true;
fail:
    return false;
}
