/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
/* Top header for AES */
#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/syscall.h"
#include "libc/random.h"
#include "drbg/drbg.h"
#include "drbg/entropy.h"

#include "autoconf.h"


/***** "Unsecure" ISO C random using a linear congruential generator (LGC) *****/
/* WARNING: this egenrator is *NOT* cryptographically secure!! */
/*
 * We use GLIBC's parameters:
 *    modulus m = 2**31
 *    multiplier a = 1103515245
 *    increment c = 12345
 *
 */
static unsigned int rand_seed = 1; /* seed default value is 1 */

int rand(void)
{
	rand_seed = (rand_seed * 1103515245) + 12345;
	return (int)((unsigned int)(rand_seed/65536) % (RAND_MAX + 1));

} 

void srand(unsigned int seed)
{
	rand_seed = seed;

	return;
}

int rand_r(unsigned int *seedp)
{
	(*seedp) = ((*seedp) * 1103515245) + 12345;
	return (int)((unsigned int)((*seedp)/65536) % (RAND_MAX + 1));
}


/***** "Secure" random using a DRBG and a TRNG *****/
/*
 * The main primitive used for our CS (Cryptographically Secure) PRNG is 
 * HMAC-DRBG as standardized bu NIST 800-90A. HMAC-DRBG has been prefered to
 * other designs (Hash-DRBG and CTR-DRG) because it has a cleaner design, and
 * inherits some security proofs (see https://www.cs.cmu.edu/~kqy/resources/thesis.pdf).
 */

#ifdef CONFIG_STD_DRBG

static volatile bool drbg_init_done = false;

#define DRBG_FRESH_ENTROPY_LEN 64
static volatile drbg_ctx random_drbg_ctx;

static int drbg_init(void)
{
	/* As a personnalisation string of the DRBG , we use the current
	 * flash address of the function (unique per task)
	 */
	unsigned char personnalisation_string[16] = { 0 };
	if(sizeof(personnalisation_string) < (4 * sizeof(void*))){
		goto err;
	}
	memcpy(personnalisation_string, (char*)&drbg_init, sizeof(void*));
	/* We also concatenate some SRAM address (also specific to the task) */
	memcpy(personnalisation_string+sizeof(void*), (char*)&drbg_init_done, sizeof(void*));
	/* Finally, we concatenate 64 bits random to make the instantiation unique */	
	if(get_entropy(personnalisation_string+(2*sizeof(void*)), (2*sizeof(void*)))){
		goto err;
	}
	/* Instantiate our DRBG context
	 * NOTE1: we do activate so called "prediction resistance" here, in order to regularly
	 * get fresh entropy. We also regularly trigger explicit reseeds
	 * using DRBG_FORCE_RESEED_INTERVAL (see below).
	 * NOTE2: we ask for a 256-bit entropy wise DRBG, yielding a HMAC-SHA256 based HMAC-DRBG.
	 */
	if(drbg_instantiate((drbg_ctx *)&random_drbg_ctx, 256, 1, personnalisation_string, sizeof(personnalisation_string)) != DRBG_OK){
		goto err;
	}

	return 0;
err:
	return -1;
}

/* Max reseeding interval (in asked bytes) for the DRBG */
#define DRBG_FORCE_RESEED_INTERVAL 128 /* Force a reseed every 128 bytes asked */

static volatile uint32_t drbg_calls = 0;
static int drbg_get_random(unsigned char *buf, uint16_t len)
{
	if(drbg_calls >= DRBG_FORCE_RESEED_INTERVAL){
		/* Time to explicitly reseed our underlying DRBG */
		unsigned char fresh_entropy[DRBG_FRESH_ENTROPY_LEN] = { 0 };
		if(get_entropy(fresh_entropy, sizeof(fresh_entropy))){
			goto err;
		}
		drbg_calls = 0;
		if(drbg_reseed((drbg_ctx*)&random_drbg_ctx, fresh_entropy, sizeof(fresh_entropy)) != DRBG_OK){
			goto err;
		}
	}
	if(drbg_generate((drbg_ctx*)&random_drbg_ctx, NULL, 0, buf, len) != DRBG_OK){
		goto err;
	}

	drbg_calls += len;

	return 0;
err:
	return -1;
}
#endif


#if __GNUC__
#pragma GCC push_options
#pragma GCC optimize("-fno-stack-protector")
#endif

#if __clang__
#pragma clang optimize off
  /* Well, clang support local stack protection deactivation only since v8 :-/ */
#if __clang_major__ > 7
#pragma clang attribute push(__attribute__((no_stack_protector)), apply_to = do_starttask)
#endif
#endif

volatile uint32_t random_secure = SEC_RANDOM_SECURE;

mbed_error_t get_random(unsigned char *buf, uint16_t len)
#ifdef CONFIG_STD_DRBG
{
        mbed_error_t err = MBED_ERROR_NONE;
        if(random_secure == SEC_RANDOM_SECURE){
            if(random_secure != SEC_RANDOM_SECURE){
                    err = MBED_ERROR_UNKNOWN;
                    goto error;
            }
  	    if(drbg_init_done == false){
	  	    if(drbg_init()){
			    err = MBED_ERROR_UNKNOWN;
  			    goto error;
  		    }
  		    drbg_init_done = true;
 	    }
  	    if(drbg_get_random(buf, len)){
	  	    err = MBED_ERROR_UNKNOWN;
  		    goto error;
	    }
       } else if(random_secure == SEC_RANDOM_NONSECURE){
            if(random_secure != SEC_RANDOM_NONSECURE){
                    err = MBED_ERROR_UNKNOWN;
                    goto error;
            }
  	    if((err = get_entropy(buf, len)) != MBED_ERROR_NONE){
		    goto error;
	    }
       }
       else{
           err = MBED_ERROR_UNKNOWN;
       }
 error:
	return err;
}
#else /* We do not use any DRBG, so we directly use the syscall to get it from kernel */
{
 	mbed_error_t err = MBED_ERROR_NONE;
	
	if((err = get_entropy(buf, len)) != MBED_ERROR_NONE){
		goto error;
	}

 error:
 	return err;
}
#endif

#if __clang__
#pragma clang optimize on
#if __clang_major__ > 7
#pragma clang attribute pop
#endif
#endif

#if __GNUC__
#pragma GCC pop_options
#endif
