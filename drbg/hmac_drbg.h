#ifndef __HMAC_DRBG_H__
#define __HMAC_DRBG_H__

#include "autoconf.h"

#ifdef CONFIG_STD_DRBG

/* Used for HMAC */
#include "hmac.h"

/* HMAC-DRBG errors */
typedef enum {
	HMAC_DRBG_OK            = 0,
	HMAC_DRBG_NON_INIT      = 1,
	HMAC_DRBG_ILLEGAL_INPUT = 2,
	HMAC_DRBG_HMAC_ERROR    = 3,
	HMAC_DRBG_NEED_RESEED   = 4,
	HMAC_DRBG_ERROR         = 5,
} hmac_drbg_error;


/* Maximum sizes in bytes, see NIST SP800-90A Table 2 */
#define MAX_ADDIN_SIZE 		((uint64_t)0x1 << 32)  /* 2**32 max */
#define MAX_ASKED_LENGTH 	(0x1 << 16) /* 2**16 bytes */
#define MAX_RESEED_INTERVAL	((uint64_t)0x1 << 48) /* 2**48 max reseed interval */

#define HMAC_DRBG_INIT_MAGIC	0x12482039

/* HMAC-DRBG context */
typedef struct {
	/* Initialization magic */
	uint32_t magic;
	/* Our hash function type */
	hash_alg_type hash_type;
	/* NOTE: MAX_DIGEST_SIZE should be exposed by the HMAC API
	 * layer.
	 */
	unsigned char K[MAX_DIGEST_SIZE];
	unsigned char V[MAX_DIGEST_SIZE];
	uint32_t digest_size;
	/*** Administration information ***/
	/* DRBG strength */
	uint32_t drbg_strength;
	uint32_t min_entropy_input_length;
	uint32_t max_entropy_input_length;
	/* Is prediction resistance enabled? */
	uint8_t prediction_resistance;
	uint64_t reseed_counter;
	uint64_t reseed_interval;
	/* Variable holding the fact that we have reseeded before a generate */
	uint8_t need_reseed;
} hmac_drbg_ctx;

/* NOTE: we could provide the exposed DRBG generic APIs as *callbacks* 
 * in the DRBG structure, which is a "clean" and usual way of abstraction.
 * However, and since we only support HMAC-DRBG (by design choice), no need
 * to use callbacks.
 */
/* Exposed API (DRBG generic APIs) */
int hmac_drbg_check_initialized(hmac_drbg_ctx *ctx);

int hmac_drbg_uninit(hmac_drbg_ctx *ctx);

hmac_drbg_error hmac_drbg_init(hmac_drbg_ctx *ctx, hash_alg_type hash_type, uint8_t prediction_resistance);

hmac_drbg_error hmac_drbg_init_with_strength(hmac_drbg_ctx *ctx, uint32_t drbg_strength, uint8_t prediction_resistance);

hmac_drbg_error hmac_drbg_instantiate(hmac_drbg_ctx *ctx, const unsigned char *data, uint32_t data_len, const unsigned char *nonce, uint32_t nonce_len, const unsigned char *addin, uint32_t addin_len);

hmac_drbg_error hmac_drbg_reseed(hmac_drbg_ctx *ctx, const unsigned char *data, uint32_t data_len, const unsigned char *addin, uint32_t addin_len);

hmac_drbg_error hmac_drbg_generate(hmac_drbg_ctx *ctx, const unsigned char *addin, uint32_t addin_len, unsigned char *out, uint32_t out_len);

hmac_drbg_error hmac_drbg_uninstantiate(hmac_drbg_ctx *ctx);

#endif /* CONFIG_STD_DRBG */

#endif /* __HMAC_DRBG_H__ */
