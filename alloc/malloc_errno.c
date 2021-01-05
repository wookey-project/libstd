#include "autoconf.h"

#include "libc/types.h"
#include "libc/sync.h"

#include "malloc_errno.h"

static uint32_t __malloc_errno;

uint32_t get_malloc_errno(void) {
    return __malloc_errno;
}

void set_malloc_errno(uint32_t value) {
    set_u32_with_membarrier(&__malloc_errno, value);
}
