#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/syscall.h"
#include "libc/random.h"

#include "entropy.h"
#include "autoconf.h"

/* TRNG entropy gatherer.
 * The following function gathers entropy form the platform TRNG
 * through the kernel using a dedicated syscall.
 */
static mbed_error_t get_trng_entropy(unsigned char *in, uint16_t len)
{
        mbed_error_t err = MBED_ERROR_NONE;
	uint8_t ret;

	if(in == NULL){
		err = MBED_ERROR_INVPARAM;
		goto error;
	}
	/* First, set the buffer to zero */
	memset(in, 0, len);
	/* Now call the platform TRNG through the dedicated syscall */
	if((ret = sys_get_random((char*)in, len)) != SYS_E_DONE){
		if(ret == SYS_E_DENIED){
			err = MBED_ERROR_DENIED;
			goto error;
		}
		else if(ret == SYS_E_BUSY){
			err = MBED_ERROR_BUSY;
			goto error;
		}
		else{
			err = MBED_ERROR_UNKNOWN;
			goto error;
		}
	}

error:
	return err;
}

/* [RB] TODO: add other entropy sources here in
 *            order to not depend only on the TRNG.
 */
/*
 * Current cycles entropy gatherer.
*/
#ifdef CONFIG_STD_DRBG_ENTROPY_CPU_CYCLES
#error "Entropy gathering through CPU cyles is not implemented yet!"
#endif

/*
 * The following function is an entropy gatherer used by DRBG layers.
 * The main entropy source is the underlying platform TRNG, but other
 * sources can be used such as CPU cycles, syscalls, and other events.
 */
mbed_error_t get_entropy(unsigned char *in, uint16_t len)
{	
        mbed_error_t err = MBED_ERROR_NONE;

	if((err = get_trng_entropy(in, len)) != MBED_ERROR_NONE){
		goto error;
	}
error:
	return err;
}
