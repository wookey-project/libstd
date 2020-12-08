#include "hmac.h"
#include "hmac_drbg.h"
#include "libc/string.h"

#ifdef CONFIG_STD_DRBG

/* HMAC-DRBG for PRNG.
 * Standardized by NIST SP 800-90A.
 */

/* Our scatter/gather structure */
#define MAX_SCATTER_DATA 5
typedef struct {
	const unsigned char *data;
	uint32_t data_len;
} in_scatter_data;

/* Internal HMAC helper */
static int hmac(hmac_context *hmac_ctx, const unsigned char *key, uint32_t key_len, const in_scatter_data *data_bag_in, unsigned int data_bag_in_num, unsigned char *output, uint32_t output_len, hash_alg_type hash_type)
{
	if(hmac_ctx == NULL){
		goto err;
	}
	if((data_bag_in == NULL) && (data_bag_in_num != 0)){
		goto err;
	}

	if(key != NULL){
		/* If the key is not NULL, initialize */
		/* Initialize our internal HMAC context with Key K */
		if(hmac_init(hmac_ctx, key, key_len, hash_type)){
			goto err;
		}
	}

	/* Update */
	if(data_bag_in == NULL){
		/* Hashing an empty string */
		unsigned char dummy;
		hmac_update(hmac_ctx, &dummy, 0);
	}
	else{
		unsigned int i;
		for(i = 0; i < data_bag_in_num; i++){
			if((data_bag_in[i].data == NULL) && (data_bag_in[i].data_len != 0)){
				goto err;
			}
			if(data_bag_in[i].data != NULL){
				hmac_update(hmac_ctx, data_bag_in[i].data, data_bag_in[i].data_len);
			}
		}
	}

	/* If output is provided, update */
	if(output != NULL){
		uint32_t len = output_len;
		if(hmac_finalize(hmac_ctx, output, &len)){
			goto err;
		}
	}

	return 0;
err:
	return -1;
}

/* The HMAC-DRBG update function */
static hmac_drbg_error hmac_drbg_update(hmac_drbg_ctx *ctx, const in_scatter_data *data_bag_in, unsigned int data_bag_in_num)
{
	hmac_drbg_error ret = HMAC_DRBG_ERROR;
	hmac_context hmac_ctx;
	unsigned int i;
	unsigned char tmp;
	in_scatter_data sc[MAX_SCATTER_DATA] = { 0 };

	if(ctx == NULL){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}
	if(hmac_drbg_check_initialized(ctx)){
		ret = HMAC_DRBG_NON_INIT;
		goto err;
	}
	if((data_bag_in == NULL) && (data_bag_in_num != 0)){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}
	if((2 + data_bag_in_num) > MAX_SCATTER_DATA){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}
	/* Compute K = H(K, V|0x00|data) */
	sc[0].data = ctx->V;
	sc[0].data_len = ctx->digest_size;
	tmp = 0x00;
	sc[1].data = &tmp;
	sc[1].data_len = sizeof(tmp);
	/* Copy the rest */
        for(i = 0; i < data_bag_in_num; i++){
                sc[2 + i] = data_bag_in[i];
	}
	if(hmac(&hmac_ctx, ctx->K, ctx->digest_size, sc, (2 + data_bag_in_num), ctx->K, ctx->digest_size, ctx->hash_type)){
		ret = HMAC_DRBG_HMAC_ERROR;
		goto err;
	}
	/* Compute V = H(K, V) */
	sc[0].data = ctx->V;
	sc[0].data_len = ctx->digest_size;
	if(hmac(&hmac_ctx, ctx->K, ctx->digest_size, sc, 1, ctx->V, ctx->digest_size, ctx->hash_type)){
		ret = HMAC_DRBG_HMAC_ERROR;
		goto err;
	}
	/* If data == NULL, then return (K, V) */
	unsigned int num_null = 0;
	for(i = 0; i < data_bag_in_num; i++){
		if((data_bag_in[i].data == NULL) || (data_bag_in[i].data_len == 0)){
			num_null++;
		}
	}
	if(num_null == data_bag_in_num){
		goto end;
	}
	/* Compute K = H(K, V|0x01|data) */
	sc[0].data = ctx->V;
	sc[0].data_len = ctx->digest_size;
	tmp = 0x01;
	sc[1].data = &tmp;
	sc[1].data_len = sizeof(tmp);
	/* Copy the rest */
        for(i = 0; i < data_bag_in_num; i++){
                sc[2 + i] = data_bag_in[i];
	}
	if(hmac(&hmac_ctx, ctx->K, ctx->digest_size, sc, (2 + data_bag_in_num), ctx->K, ctx->digest_size, ctx->hash_type)){
		ret = HMAC_DRBG_HMAC_ERROR;
		goto err;
	}
	/* Compute V = H(K, V) */
	sc[0].data = ctx->V;
	sc[0].data_len = ctx->digest_size;
	if(hmac(&hmac_ctx, ctx->K, ctx->digest_size, sc, 1, ctx->V, ctx->digest_size, ctx->hash_type)){
		ret = HMAC_DRBG_HMAC_ERROR;
		goto err;
	}

end:
	return HMAC_DRBG_OK;
err:
	return ret;
}

static int hmac_drbg_get_strength(hash_alg_type hash_type, uint32_t *drbg_strength, uint32_t *digest_size, uint32_t *block_size)
{
	uint8_t ds, bs;

	if(drbg_strength == NULL){
		goto err;
	}

	if(get_hash_sizes(hash_type, &ds, &bs)){
		goto err;
	}
	if(digest_size != NULL){
		(*digest_size) = ds;
	}
	if(block_size != NULL){
		(*block_size) = bs;
	}

	if(ds <= 20){
		/* 128 bits strength */
		(*drbg_strength) = 128;
	}
	else if(ds <= 28){
		/* 192 bits strength */
		(*drbg_strength) = 192;
	}
	else{
		/* 256 bits strength */
		(*drbg_strength) = 256;
	}

	return 0;
err:
	return -1;
}

/* External API */
int hmac_drbg_check_initialized(hmac_drbg_ctx *ctx)
{
	if(ctx == NULL){
		goto err;
	}
	if(ctx->magic != HMAC_DRBG_INIT_MAGIC){
		goto err;
	}

	return 0;
err:
	return -1;
}


int hmac_drbg_uninit(hmac_drbg_ctx *ctx)
{
	if(ctx == NULL){
		goto err;
	}
	ctx->magic = 0x0;

	return 0;
err:
	return -1;
}

hmac_drbg_error hmac_drbg_init(hmac_drbg_ctx *ctx, hash_alg_type hash_type, uint8_t prediction_resistance)
{
	hmac_drbg_error ret = HMAC_DRBG_ERROR;

	if(ctx == NULL){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}

	ctx->magic = HMAC_DRBG_INIT_MAGIC;

	ctx->hash_type = hash_type;
	/* Compute the strength */
	if(hmac_drbg_get_strength(hash_type, &(ctx->drbg_strength), &(ctx->digest_size), NULL)){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}

	ctx->reseed_counter = 0;
	ctx->prediction_resistance = (prediction_resistance == 0) ? 0 : 1;
	/* Initialize stuff provided by NIST SP800-90A in table 2 */
	/* Initialize reseed interval */
	ctx->reseed_interval = MAX_RESEED_INTERVAL;
	ctx->min_entropy_input_length = ctx->max_entropy_input_length = (ctx->drbg_strength / 8);

	return HMAC_DRBG_OK;
err:
	return ret;
}

hmac_drbg_error hmac_drbg_init_with_strength(hmac_drbg_ctx *ctx, uint32_t drbg_strength, uint8_t prediction_resistance)
{
	hmac_drbg_error ret = HMAC_DRBG_ERROR;

	/* Map best hash function to strength */
	if(drbg_strength <= 192){
#if defined(WITH_HASH_SHA224)
		if((ret = hmac_drbg_init(ctx, SHA224, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#elif defined(WITH_HASH_SHA256)
		if((ret = hmac_drbg_init(ctx, SHA256, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#elif defined(WITH_HASH_SHA384)
		if((ret = hmac_drbg_init(ctx, SHA384, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#elif defined(WITH_HASH_SHA512)
		if((ret = hmac_drbg_init(ctx, SHA512, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#else
		goto err;
#endif
	}
	else if(drbg_strength <= 256){
#if defined(WITH_HASH_SHA256)
		if((ret = hmac_drbg_init(ctx, SHA256, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#elif defined(WITH_HASH_SHA384)
		if((ret = hmac_drbg_init(ctx, SHA384, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#elif defined(WITH_HASH_SHA512)
		if((ret = hmac_drbg_init(ctx, SHA512, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#else
		goto err;
#endif
	}
	else{
#if defined(WITH_HASH_SHA512)
		if((ret = hmac_drbg_init(ctx, SHA512, prediction_resistance)) != HMAC_DRBG_OK){
			goto err;
		}
#else
		goto err;
#endif
	}

	return HMAC_DRBG_OK;
err:
	return ret;
}


hmac_drbg_error hmac_drbg_instantiate(hmac_drbg_ctx *ctx, const unsigned char *data, uint32_t data_len, const unsigned char *nonce, uint32_t nonce_len, const unsigned char *addin, uint32_t addin_len)
{
	hmac_drbg_error ret = HMAC_DRBG_ERROR;
	in_scatter_data sc[3] = { 0 };

	if((ctx == NULL) || (data == NULL) || (data_len == 0)){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}
	if(hmac_drbg_check_initialized(ctx)){
		ret = HMAC_DRBG_NON_INIT;
		goto err;
	}
	/* Should not happen thanks to uint32_t type, but check anyways ... */
	if(((uint64_t)addin_len + 1) > (MAX_ADDIN_SIZE + 1)){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}

	/* Initialize K with 0x000 ... 00 */
	memset(ctx->K, 0x00, ctx->digest_size);
	/* Initialize V with 0x0101  ... 01 */
	memset(ctx->V, 0x01, ctx->digest_size);
	/* Initialize reseed counter with 1 */
	ctx->reseed_counter = 1;
	/* Initialize need reseed */
	ctx->need_reseed = 1;

	/* (K, V) = update(seed_material, K, V))
	 * with seed_material = data | nonce | addin
	 */
	sc[0].data = data;
	sc[0].data_len = data_len;
	sc[1].data = nonce;
	sc[1].data_len = nonce_len;
	sc[2].data = addin;
	sc[2].data_len = addin_len;
	if((ret = hmac_drbg_update(ctx, sc, 3)) != HMAC_DRBG_OK){
		ret = HMAC_DRBG_HMAC_ERROR;
		goto err;
	}

	return HMAC_DRBG_OK;
err:
	return ret;
}


hmac_drbg_error hmac_drbg_uninstantiate(hmac_drbg_ctx *ctx)
{
	hmac_drbg_error ret = HMAC_DRBG_ERROR;

	if(hmac_drbg_uninit(ctx)){
		goto err;
	}
	/* Cleanup stuff inside our state */
	memset(ctx->K, 0x00, sizeof(ctx->K));
	memset(ctx->V, 0x00, sizeof(ctx->V));
	ctx->reseed_counter = ctx->reseed_interval = ctx->need_reseed = 0;

	return HMAC_DRBG_OK;
err:
	return ret;
}

hmac_drbg_error hmac_drbg_reseed(hmac_drbg_ctx *ctx, const unsigned char *data, uint32_t data_len, const unsigned char *addin, uint32_t addin_len)
{
	hmac_drbg_error ret = HMAC_DRBG_ERROR;
	in_scatter_data sc[2] = { 0 };

	if((ctx == NULL) || (data == NULL) || (data_len == 0)){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}
	if(hmac_drbg_check_initialized(ctx)){
		ret = HMAC_DRBG_NON_INIT;
		goto err;
	}
	/* Should not happen thanks to uint32_t type, but check anyways ... */
	if(((uint64_t)addin_len + 1) > (MAX_ADDIN_SIZE + 1)){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}

	/* Initialize reseed counter with 1 */
	ctx->reseed_counter = 1;
	/* Notify that we have reseeded */
	ctx->need_reseed = 0;

	/* (K, V) = update(seed_material, K, V))
	 * with seed_material = data | addin
	 */
	sc[0].data = data;
	sc[0].data_len = data_len;
	sc[1].data = addin;
	sc[1].data_len = addin_len;
	if((ret = hmac_drbg_update(ctx, sc, 2)) != HMAC_DRBG_OK){
		goto err;
	}

	return HMAC_DRBG_OK;
err:
	return ret;
}

hmac_drbg_error hmac_drbg_generate(hmac_drbg_ctx *ctx, const unsigned char *addin, uint32_t addin_len, unsigned char *out, uint32_t out_len)
{
	hmac_drbg_error ret = HMAC_DRBG_ERROR;
	hmac_context hmac_ctx;
	in_scatter_data sc[1] = { 0 };

	if(ctx == NULL){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}
	if(hmac_drbg_check_initialized(ctx)){
		ret = HMAC_DRBG_NON_INIT;
		goto err;
	}
	if(ctx->reseed_counter < 1){
		/* DRBG not seeded yet! */
		ret = HMAC_DRBG_NON_INIT;
		goto err;
	}
	/* Should not happen thanks to uint32_t type, but check anyways ... */
	if(((uint64_t)addin_len + 1) > (MAX_ADDIN_SIZE + 1)){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}
	if(out_len > MAX_ASKED_LENGTH){
		ret = HMAC_DRBG_ILLEGAL_INPUT;
		goto err;
	}

	if((ctx->reseed_counter > ctx->reseed_interval) || ((ctx->prediction_resistance != 0) && (ctx->need_reseed != 0))){
		ret = HMAC_DRBG_NEED_RESEED;
		goto err;
	}

	/* (K, V) = update(addin, K, V) if addin != NULL */
	if((addin != NULL) && (addin_len != 0)){
		sc[0].data = addin;
		sc[0].data_len = addin_len;
		if((ret = hmac_drbg_update(ctx, sc, 1)) != HMAC_DRBG_OK){
			goto err;
		}
	}

	uint32_t generated = 0;
	/* Generate he bitstream until we have enough data */
	while(generated < out_len){
		/* Compute V = H(K, V) */
		sc[0].data = ctx->V;
		sc[0].data_len = ctx->digest_size;
		if(hmac(&hmac_ctx, ctx->K, ctx->digest_size, sc, 1, ctx->V, ctx->digest_size, ctx->hash_type)){
			ret = HMAC_DRBG_HMAC_ERROR;
			goto err;
		}
		/* Copy V in output */
		unsigned int size_to_copy = ((out_len - generated) < ctx->digest_size) ? (out_len - generated) : ctx->digest_size;
		memcpy((out + generated), ctx->V, size_to_copy);
		generated += ctx->digest_size;
	}

	/* (K, V) = update(addin, K, V) */
	sc[0].data = addin;
	sc[0].data_len = addin_len;
	if((ret = hmac_drbg_update(ctx, sc, 1)) != HMAC_DRBG_OK){
		goto err;
	}
	/* Update the reseed counter */
	ctx->reseed_counter++;
	ctx->need_reseed++;

	return HMAC_DRBG_OK;
err:
	return ret;
}

#endif /* CONFIG_STD_DRBG */
