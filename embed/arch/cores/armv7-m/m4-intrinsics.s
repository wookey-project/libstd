.syntax unified
.cpu cortex-m4
.fpu softvfp
.thumb


.section .text
.global __BKPT

.global __DMB
.global __IMB

.global __STREXW
.global __STREXH
.global __STREXB

.type __BKPT,   %function
.type __STREXW, %function
.type __STREXH, %function
.type __STREXB, %function

__DSB:
    dsb

__DMB:
    dmb

__ISB:
    isb

__BKPT:
    bkpt

__STREXW:
    push {r1,r2}
    strex r2, r0, [r1]
    dmb
    cmp r2,#0
    beq fail__strexw
    pop {r1,r2}
    mov r0, #0
    bx lr
fail__strexw:
    pop {r1,r2}
    mov r0, #1
    bx lr

__STREXH:
    push {r1,r2}
    strexh r2, r0, [r1]
    dmb
    cmp r2,#0
    beq fail__strexh
    pop {r1,r2}
    mov r0, #0
    bx lr
fail__strexh:
    pop {r1,r2}
    mov r0, #1
    bx lr

__STREXB:
    push {r1,r2}
    strexb r2, r0, [r1]
    dmb
    cmp r2,#0
    beq fail__strexb
    pop {r1,r2}
    mov r0, #0
    bx lr
fail__strexb:
    pop {r1,r2}
    mov r0, #1
    bx lr
