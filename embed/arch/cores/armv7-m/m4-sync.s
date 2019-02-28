.syntax unified
.cpu cortex-m4
.fpu softvfp
.thumb


.section .text
.global core_semaphore_trylock
.global core_semaphore_release

.type  core_semaphore_trylock, %function
.type  core_semaphore_release, %function

core_semaphore_trylock:
    push    {r1,r2}
    ldrex   r1, [r0]
    cmp     r1, #0        /* Test if semaphore holds the value 0 */
                          /* If it does, block before retrying */
    beq     fail_core_semaphore_trylock
    sub     r1, #1        /* If not, decrement temporary copy */
    strex   r2, r1, [r0]  /* Attempt Store-Exclusive */
    cmp     r2, #0        /* Check if Store-Exclusive succeeded */
                          /* If Store-Exclusive failed, retry from start */
    bne     fail_core_semaphore_trylock
    dmb                   /*  Required before accessing protected resource */
    pop {r1,r2}
    mov r0, #1
    bx lr
fail_core_semaphore_trylock:
    pop {r1,r2}
    mov r0, #0
    bx lr


core_semaphore_release:
    push {r1,r2}
    ldrex   r1, [r0]
    add     r1, #1        /* Increment temporary copy */
    strex   r2, r1, [r0]  /* Attempt Store-Exclusive  */
    cmp     r2, #0        /* Check if Store-Exclusive succeeded */
                          /* If Store-Exclusive failed, retry from start */
    bne     fail_core_semaphore_release
    dmb                   /* Required before accessing protected resource */
    pop {r1,r2}
    mov r0, #1
    bx lr
fail_core_semaphore_release:
    pop {r1,r2}
    mov r0, #0
    bx lr

.end
