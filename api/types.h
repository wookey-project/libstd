#ifndef TYPES_H_
#define TYPES_H_

#include "autoconf.h"

#ifdef CONFIG_ARCH_ARMV7M
# include "arch/cores/armv7-m/types.h"
#else
# error "architecture not yet supported"
#endif

typedef enum {false = 0, true = 1} bool;

#if defined(__CC_ARM)
# define __ASM            __asm  /* asm keyword for ARM Compiler    */
# define __INLINE         static __inline    /* inline keyword for ARM Compiler */
# define __UNUSED                /* [PTH] todo: find the way to set a function/var unused */
#elif defined(__GNUC__)
# define __ASM            __asm  /* asm keyword for GNU Compiler    */
# define __INLINE        static inline
# define __UNUSED        __attribute__((unused))
# define __packed		__attribute__((__packed__))
#endif

#define __in            /* indication for function arguments (Ada like) */
#define __out           /* indication for function arguments (Ada like) */
#define __inout         /* indication for function arguments (Ada like) */

#endif/*!TYPES_H_*/
