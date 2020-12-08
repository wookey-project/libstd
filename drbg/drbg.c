#include "drbg/drbg.h"
#include "libc/string.h"

#ifdef CONFIG_STD_DRBG

/* Entropy gathering function */
#include "drbg/entropy.h"


/* DRBG for PRNG.
 * Standardized by NIST SP 800-90A.
 * As for now, we only support HMAC-DRBG as a backend.
 */

static int drbg_check_initialized(drbg_ctx *ctx)
{
        if(ctx == NULL){
                goto err;
        }
        if(ctx->magic != DRBG_INIT_MAGIC){
                goto err;
        }
	if(backend_drbg_check_initialized(&(ctx->drbg_ctx))){
		goto err;
	}

        return 0;
err:
        return -1;
}

static int drbg_uninit(drbg_ctx *ctx)
{
        if(ctx == NULL){
                goto err;
        }
        ctx->magic = 0x0;
	if(backend_drbg_uninit(&(ctx->drbg_ctx))){
		goto err;
	}

        return 0;
err:
        return -1;
}

static int drbg_init(drbg_ctx *ctx)
{
        if(ctx == NULL){
                goto err;
        }

        ctx->magic = DRBG_INIT_MAGIC;

        return 0;
err:
        return -1;
}

/* DRBG instantiate */
drbg_error drbg_instantiate(drbg_ctx *ctx, uint32_t requested_instantiation_security_strength, uint8_t prediction_resistance, const unsigned char *personalization_string, uint32_t personalization_string_len)
{
	drbg_error ret = DRBG_ERROR;
	unsigned char *data;
	uint32_t data_len;
	unsigned char *Nonce;
	uint32_t NonceLen;


	if(drbg_init(ctx)){
		ret = DRBG_NON_INIT;
		goto err;
	}
	/* Find the most suitable backend variant with our requested_instantiation_security_strength */
	if(backend_drbg_init_with_strength(&(ctx->drbg_ctx), requested_instantiation_security_strength, prediction_resistance) != BACKEND_DRBG_OK){
		ret = DRBG_BACKEND_ERROR;
		goto err;
	}

	/* Instantiate our underlying DRBG */
	if((2*ctx->drbg_ctx.min_entropy_input_length) > sizeof(ctx->entropy_pool)){
		ret = DRBG_ENTROPY_ERROR;
		goto err;
	}
	/* First, get some entropy input and the nonce */
	if(get_entropy(ctx->entropy_pool, (2 * ctx->drbg_ctx.min_entropy_input_length))){
		ret = DRBG_ENTROPY_ERROR;
		goto err;
	}
	data = ctx->entropy_pool;
	data_len = ctx->drbg_ctx.min_entropy_input_length;
	Nonce = ctx->entropy_pool + data_len;
	NonceLen = ctx->drbg_ctx.min_entropy_input_length;
	/* Now instantiate the HMAC drbg */
	if(backend_drbg_instantiate(&(ctx->drbg_ctx), data, data_len, Nonce, NonceLen, personalization_string, personalization_string_len) != BACKEND_DRBG_OK){
		ret = DRBG_BACKEND_ERROR;
		goto err;
	}

	return DRBG_OK;
err:
	/* Cleanup local entropy pool in all cases */
	memset(ctx->entropy_pool, 0, sizeof(ctx->entropy_pool));
	return ret;
}

/* DRBG reseed */
drbg_error drbg_reseed(drbg_ctx *ctx, const unsigned char *addin, uint32_t addin_len)
{
	drbg_error ret = DRBG_ERROR;
	unsigned char *data;
	uint32_t data_len;

	if(drbg_check_initialized(ctx)){
		ret = DRBG_NON_INIT;
		goto err;
	}
	/* Get entropy */
	if(ctx->drbg_ctx.min_entropy_input_length > sizeof(ctx->entropy_pool)){
		ret = DRBG_ENTROPY_ERROR;
		goto err;
	}
	if(get_entropy(ctx->entropy_pool, ctx->drbg_ctx.min_entropy_input_length)){
		ret = DRBG_ENTROPY_ERROR;
		goto err;
	}
	data = ctx->entropy_pool;
	data_len = ctx->drbg_ctx.min_entropy_input_length;
	/* Call the underlying backend reseed function */
	/* NOTE: size of additional input is cheched by the backend */
	if(backend_drbg_reseed(&(ctx->drbg_ctx), data, data_len, addin, addin_len) != BACKEND_DRBG_OK){
		ret = DRBG_BACKEND_ERROR;
		goto err;
	}

	return DRBG_OK;
err:
	/* Cleanup local entropy pool in all cases */
	memset(ctx->entropy_pool, 0, sizeof(ctx->entropy_pool));
	return ret;
}

/* DRBG generate */
drbg_error drbg_generate(drbg_ctx *ctx, const unsigned char *addin, uint32_t addin_len, unsigned char *out, uint32_t out_len)
{
	drbg_error ret = DRBG_ERROR;
	backend_drbg_error backend_ret;

	if(drbg_check_initialized(ctx)){
		ret = DRBG_NON_INIT;
		goto err;
	}
	/* Call our backend */
	/* NOTE: size of additional input is checked by the backend */
gen_again:
	if((backend_ret = backend_drbg_generate(&(ctx->drbg_ctx), addin, addin_len, out, out_len)) != BACKEND_DRBG_OK){
		if(backend_ret == BACKEND_DRBG_NEED_RESEED){
			/* We are asked for a reseed, perform one */
			if((ret = drbg_reseed(ctx, NULL, 0)) != DRBG_OK){
				goto err;
			}
			/* Now ask for generate again */
			goto gen_again;
		}
		else{
			ret = DRBG_BACKEND_ERROR;
			goto err;
		}
	}

	return DRBG_OK;
err:
	return ret;
}

/* DRBG uninstantiate */
drbg_error drbg_uninstantiate(drbg_ctx *ctx)
{
	drbg_error ret = DRBG_ERROR;

	if(drbg_check_initialized(ctx)){
		ret = DRBG_NON_INIT;
		goto err;
	}
	/* Cleanup our local entropy pool */
	memset(ctx->entropy_pool, 0, sizeof(ctx->entropy_pool));
	if(backend_drbg_uninstantiate(&(ctx->drbg_ctx)) != BACKEND_DRBG_OK){
		ret = DRBG_BACKEND_ERROR;
		goto err;
	}
	if(drbg_uninit(ctx)){
		goto err;
	}

	return DRBG_OK;
err:
	return ret;
}

#endif /* CONFIG_STD_DRBG */
