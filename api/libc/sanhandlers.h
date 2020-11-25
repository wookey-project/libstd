#ifndef __SANHANDLERS_H__
#define __SANHANDLERS_H__

#include "autoconf.h"
#include "libc/syscall.h"

#ifdef CONFIG_STD_SANITIZE_HANDLERS

/*
 * INFO: when using FramaC, do not use sanhandlers API as this API is using ldscript based mechanism to check symbol allocation,
 * using void* cast. This mechanism is **NOT** Frama-C compliant.
 */

#define CONCAT_(x,y) x##y
#define CONCAT(x,y) CONCAT_(x,y)

/* Add a handler to the registered ones */
#define ADD_LOC_HANDLER(a) do {             \
        __attribute__ ((section ("SEC_sanhandlers"))) __attribute__((used)) static void* handler = (void*)(a);     \
} while(0);

#define ADD_GLOB_HANDLER(a) \
        __attribute__ ((section ("SEC_sanhandlers"))) __attribute__((used)) static void* CONCAT(handler,__LINE__) = (void*)(a);


/* Check if a handler is in our approved handlers */
extern physaddr_t __s_SEC_sanhandlers;
extern physaddr_t __e_SEC_sanhandlers;

static inline int handler_sanity_check(physaddr_t h)
{
        physaddr_t *start = &__s_SEC_sanhandlers;
        physaddr_t *end   = &__e_SEC_sanhandlers;
        while(start < end){
		if(h == *start){
			return 0;
		}
		start++;
	}

	return -1;
}

/* Check handler with panic */

static inline int handler_sanity_check_with_panic(physaddr_t h)
{
	if(handler_sanity_check(h)){
		sys_panic();
		/* This should not happen, but protect anyways */
#ifndef __FRAMAC__
		while(1){};
#endif
	}
	else{
		return 0;
	}
	/* This should not happen, but protect anyways */
#ifndef __FRAMAC__
	while(1){};
#endif
    return 0;
}

#else /* !CONFIG_STD_SANITIZE_HANDLERS */

#define ADD_LOC_HANDLER(a)

#define ADD_GLOB_HANDLER(a)

static inline int handler_sanity_check(__attribute__((unused)) physaddr_t h)
{
	return 0;
}

static inline int handler_sanity_check_with_panic(__attribute__((unused)) physaddr_t h)
{
	return 0;
}

#endif /* CONFIG_STD_SANITIZE_HANDLERS */

#endif /* __SANHANDLERS_H__ */
