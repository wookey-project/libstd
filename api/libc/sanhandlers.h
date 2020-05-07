#ifndef __SANHANDLERS_H__
#define __SANHANDLERS_H__

#include "autoconf.h"

#ifdef CONFIG_STD_SANITIZE_HANDLERS

#define CONCAT_(x,y) x##y
#define CONCAT(x,y) CONCAT_(x,y)

/* Add a handler to the registered ones */
#define ADD_LOC_HANDLER(a) do {             \
        __attribute__ ((section ("SEC_sanhandlers"))) __attribute__((used)) static void* handler = (void*)(a);     \
} while(0);

#define ADD_GLOB_HANDLER(a) \
        __attribute__ ((section ("SEC_sanhandlers"))) __attribute__((used)) static void* CONCAT(handler,__LINE__) = (void*)(a);   


/* Check if a handler is in our approved handlers */
extern void *__s_SEC_sanhandlers;
extern void *__e_SEC_sanhandlers;

static inline int handler_sanity_check(void *h)
{
        void **start = &__s_SEC_sanhandlers;
        void **end   = &__e_SEC_sanhandlers;
        while(start < end){
		if(h == *start){
			return 0;
		}
		start++;
	}

	return -1;
}

#else /* !CONFIG_STD_SANITIZE_HANDLERS */

#define ADD_LOC_HANDLER(a)

#define ADD_GLOB_HANDLER(a)

static inline int handler_sanity_check(__attribute__((unused)) void *h)
{
	return 0;
}


#endif /* CONFIG_STD_SANITIZE_HANDLERS */

#endif /* __SANHANDLERS_H__ */
