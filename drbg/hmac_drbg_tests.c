#ifdef HMAC_DRBG_SELF_TESTS

#include "hmac_drbg_tests.h"

static void hexdump(const char* prefix, const char *in, unsigned int len){
	unsigned int i;
	if(prefix != NULL){
		printf("%s", prefix);
	}
	if(in != NULL){
		for(i = 0; i < len; i++){
			printf("%02x", (unsigned char)in[i]);
		}
		printf("\n");
	}
}

static const char *get_op_name(hmac_dbrg_self_test_op op){
	switch(op){
		case GENERATE:
			return "GENERATE";
		case INSTANTIATE:
			return "INSTANTIATE";
		case RESEED_EXPLICIT:
			return "RESEED_EXPLICIT";
		case RESEED_PR:
			return "RESEED_PR";
		default:
			return "UNKNOWN_OP";
	}
}

#define MAX_OUT_SIZE 2048

int do_hmac_dbrg_self_tests(const hmac_dbrg_self_test *all_tests, unsigned int num_tests){
	unsigned int i, j;
	hmac_drbg_ctx ctx_;
	hmac_drbg_ctx *ctx = &ctx_;

	for(i = 0; i < num_tests; i++){
		const char *name = all_tests[i].name;
		printf("\n\t=========== Testing %s\n", name);
		/* Initialize our context */
		hmac_drbg_init(ctx, all_tests[i].hash, all_tests[i].prediction_resistance); 
		/* Parse all our tests */
		for(j = 0; j < all_tests[i].num_gen; j++){
		        hmac_dbrg_self_test_op op = all_tests[i].Expected[j].op;
			const unsigned char *EntropyInput = (const unsigned char*)all_tests[i].Expected[j].EntropyInput;
			uint32_t EntropyInputLen = all_tests[i].Expected[j].EntropyInputLen;
			const unsigned char *Nonce = (const unsigned char*)all_tests[i].Expected[j].Nonce;
			uint32_t NonceLen = all_tests[i].Expected[j].NonceLen;
			const unsigned char *PersonalizationString = (const unsigned char*)all_tests[i].Expected[j].PersonalizationString;
			uint32_t PersonalizationStringLen = all_tests[i].Expected[j].PersonalizationStringLen;
			const unsigned char *AdditionalInput = (const unsigned char*)all_tests[i].Expected[j].AdditionalInput;
			uint32_t AdditionalInputLen = all_tests[i].Expected[j].AdditionalInputLen;
			const unsigned char *AdditionalInputReseed = (const unsigned char*)all_tests[i].Expected[j].AdditionalInputReseed;
			uint32_t AdditionalInputReseedLen = all_tests[i].Expected[j].AdditionalInputReseedLen;
			const unsigned char *EntropyInputPR = (const unsigned char*)all_tests[i].Expected[j].EntropyInputPR;
			uint32_t EntropyInputPRLen = all_tests[i].Expected[j].EntropyInputPRLen;
			const unsigned char *EntropyInputReseed = (const unsigned char*)all_tests[i].Expected[j].EntropyInputReseed;
			uint32_t EntropyInputReseedLen = all_tests[i].Expected[j].EntropyInputReseedLen;
			const unsigned char *V = (const unsigned char*)all_tests[i].Expected[j].V;
			const unsigned char *K = (const unsigned char*)all_tests[i].Expected[j].K;
			const unsigned char *expected_out = (const unsigned char*)all_tests[i].Expected[j].out;
			unsigned char output[MAX_OUT_SIZE];
			uint32_t outlen = all_tests[i].Expected[j].outlen;

			if(MAX_OUT_SIZE < outlen){
				/* Size overflow ... */
				printf("Output size overflow ...\n");
				goto err;
			}

			if(op == INSTANTIATE){
				/* Instantiate */
				printf("[INSTANTIATE]\n");
				if(hmac_drbg_instantiate(ctx, EntropyInput, EntropyInputLen, Nonce, NonceLen, PersonalizationString, PersonalizationStringLen) != HMAC_DRBG_OK){
					printf("Error in INSTANTIATE\n");
					goto err;
				}
			}
			if(op == RESEED_EXPLICIT){
				printf("[RESEED (explicit)]\n");
				/* Explicitly call reseed */
				if(hmac_drbg_reseed(ctx, EntropyInputReseed, EntropyInputReseedLen, AdditionalInputReseed, AdditionalInputReseedLen) != HMAC_DRBG_OK){
					printf("Error in RESEED_EXPLICIT\n");
					goto err;
				}
			}
			if(op == RESEED_PR){
				printf("[RESEED (PR)]\n");
				/* Explicitly call reseed */
				if(hmac_drbg_reseed(ctx, EntropyInputPR, EntropyInputPRLen, AdditionalInput, AdditionalInputLen) != HMAC_DRBG_OK){
					printf("Error in RESEED_PR\n");
					goto err;
				}
			}
			if(op == GENERATE){
				printf("[GENERATE %d bytes]\n", outlen);
				if(hmac_drbg_generate(ctx, AdditionalInput, AdditionalInputLen, output, outlen) != HMAC_DRBG_OK){
					printf("Error in GENERATE\n");
					goto err;
				}
			}

			/* Check internal state and output if necessary */
#ifdef HMAC_DRBG_SELF_TESTS_VERBOSE
			hexdump("\tV  = ", (const char*)ctx->V, ctx->digest_size);
			hexdump("\tK  = ", (const char*)ctx->K, ctx->digest_size);
#endif
			if((local_strlen((const char*)V) != 0) && (local_strlen((const char*)K) != 0)){
				if((!are_equal(ctx->V, V, ctx->digest_size)) || (!are_equal(ctx->K, K, ctx->digest_size))){
					printf("Error for K or V after operations #%d  (type %s) for %s\n", j, get_op_name(op), name);
#ifdef HMAC_DRBG_SELF_TESTS_VERBOSE
					hexdump("\t(expected) V  = ", (const char*)V, ctx->digest_size);
					hexdump("\t(expected) K  = ", (const char*)K, ctx->digest_size);
#endif
					goto err;
				}
			}
			if(local_strlen(((const char*)expected_out)) > 0){
#ifdef HMAC_DRBG_SELF_TESTS_VERBOSE
				hexdump("\tout= ", (const char*)output, outlen);
#endif

				if(!are_equal(output, expected_out, outlen)){
					printf("Error for output after operations #%d  (type %s) for %s\n", j, get_op_name(op), name);
#ifdef HMAC_DRBG_SELF_TESTS_VERBOSE
					hexdump("\t(expected) out  = ", (const char*)expected_out, outlen);
#endif
					goto err;
				}
			}
		}
		/* Uninstantiate */
		hmac_drbg_uninstantiate(ctx);	
	}
	printf("\n-----------------------------\n");
	printf("[+] All tests are OK! :-)\n");
	printf("    (%d tests performed)\n", num_tests);

	return 0;
err:
	return -1;
}

#endif

