#ifndef __DRBG_H__
#define __DRBG_H__

#include "autoconf.h"

#ifdef CONFIG_STD_DRBG

#ifdef CONFIG_USR_LIB_DRBG_USE_HMAC_DRBG
/* Used for HMAC-DRBG */
#include "hmac_drbg.h"
/* Aliases for backend functions and errors */
/****************/
#define backend_drbg_check_initialized hmac_drbg_check_initialized
#define backend_drbg_init_with_strength	hmac_drbg_init_with_strength
#define backend_drbg_init hmac_drbg_init
#define backend_drbg_uninit hmac_drbg_uninit
#define backend_drbg_init_with_strength hmac_drbg_init_with_strength
#define backend_drbg_instantiate hmac_drbg_instantiate
#define backend_drbg_reseed hmac_drbg_reseed
#define backend_drbg_generate hmac_drbg_generate
#define backend_drbg_uninstantiate hmac_drbg_uninstantiate
/* */
#define backend_drbg_error		hmac_drbg_error
/* */
#define BACKEND_DRBG_OK			HMAC_DRBG_OK
#define BACKEND_DRBG_NEED_RESEED	HMAC_DRBG_NEED_RESEED
/****************/
#else
#error "No DRBG backend has been selected ... Please chose one!"
#error "Available backends are: HMAC-DRBG"
#endif


/* DRBG errors */
typedef enum {
        DRBG_OK             = 0,
        DRBG_NON_INIT       = 1,
        DRBG_ILLEGAL_INPUT  = 2,
        DRBG_BACKEND_ERROR  = 3,
        DRBG_ENTROPY_ERROR  = 4,
        DRBG_ERROR          = 5,
} drbg_error;

#define DRBG_INIT_MAGIC    0x19634222

#define ENTROPY_POOL_LEN	1024

/* HMAC-DRBG context */
typedef struct {
        /* Initialization magic */
        uint32_t magic;
	/* Entropy gatherer */
	unsigned char entropy_pool[ENTROPY_POOL_LEN];
#ifdef CONFIG_USR_LIB_DRBG_USE_HMAC_DRBG
	/* NOTE: other DRBG backends could be used
	 */
	hmac_drbg_ctx drbg_ctx;
#endif
} drbg_ctx;


drbg_error drbg_instantiate(drbg_ctx *ctx, uint32_t requested_instantiation_security_strength, uint8_t prediction_resistance, const unsigned char *personalization_string, uint32_t personalization_string_len);

drbg_error drbg_reseed(drbg_ctx *ctx, const unsigned char *addin, uint32_t addin_len);

drbg_error drbg_generate(drbg_ctx *ctx, const unsigned char *addin, uint32_t addin_len, unsigned char *out, uint32_t out_len);

drbg_error drbg_uninstantiate(drbg_ctx *ctx);

#endif /* CONFIG_STD_DRBG */

#endif /* __DRBG_H__ */
