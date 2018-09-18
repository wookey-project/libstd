#ifndef H_ERRNO
#define H_ERRNO

#include "autoconf.h"

#ifdef TEST_X86
#include <errno.h>
#else
#include "api/types.h"
volatile uint32_t errno;
#endif

/* for EwoK */

#define EHEAPNOMEM          140     /* Not enough space in heap */
#define EHEAPFULL           141     /* Heap is totally full */
#define EHEAPINTEGRITY      142     /* Heap could be corrupted */
#define EHEAPLOCKED         143     /* WMalloc is already locked */
#define EHEAPALREADYALLOC   144     /* Pointer already allocated */
#define EHEAPALREADYFREE    145     /* Pointer not allocated */
#define EHEAPOUTOFRANGE     146     /* Address out of range */
#define EHEAPFLAGNOTVALID   147     /* Flag not valid */
#define EHEAPNODEF          148     /* Not defined error */
#define EHEAPSEMAPHORE      149     /* Error in wmalloc locking/unlocking */
#define EHEAPSIZETOOSMALL   150     /* Heap's size is too big (HEAP_SIZE_LEN could be changed) */
#define EHEAPSIZETOOBIG     151     /* Heap's size is too big (HEAP_SIZE_LEN could be changed) */
#define EHEAPSIZENOTALIGNED 152     /* Heap's size not aligned (HEAP_ALIGN could be changed) */

#define EMEMDESTNULL        160     /* Destination pointer null */
#define EMEMHEAPUNDERFLOW   161     /* Execution would cause a heap underflow */
#define EMEMHEAPOVERFLOW    162     /* Execution would cause a heap overflow */
#define EMEMHEAPWRITEFREE   163     /* Trying to write into free block */

#define EPROTECNOTACTIVE    170     /* Selected protection was not activated */

#define ESTRTOLBASE         180     /* Base unexpected */
#define ESTRTOLLONG         181     /* String too long to be converted into integer */
#define ESTRTOLBADCHAR      182     /* String contains unconvertible characters */
#define ESTRTOLCHECK        183     /* Checking of integer negative */


#endif

