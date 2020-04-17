#ifndef __HMAC_DRBG_TESTS_H__

#ifdef HMAC_DRBG_SELF_TESTS
#include "hmac_drbg.h"

typedef enum {
        INSTANTIATE     = 0,
        RESEED_EXPLICIT = 1,
        RESEED_PR       = 2,
        GENERATE        = 3
} hmac_dbrg_self_test_op;
typedef struct {
        hmac_dbrg_self_test_op op;
        const char *EntropyInput;
	uint32_t EntropyInputLen;
        const char *Nonce;
	uint32_t NonceLen;
        const char *PersonalizationString;
	uint32_t PersonalizationStringLen;
        const char *AdditionalInput;
	uint32_t AdditionalInputLen;
        const char *EntropyInputPR;
	uint32_t EntropyInputPRLen;
        const char *EntropyInputReseed;
	uint32_t EntropyInputReseedLen;
        const char *AdditionalInputReseed;
	uint32_t AdditionalInputReseedLen;
        /* Expected out */
        const char *V;
        const char *K;
        uint32_t outlen;
        const char *out;
} hmac_dbrg_self_test_expected;
typedef struct {
        const char *name;
        hash_alg_type hash;
        uint8_t prediction_resistance;
        unsigned int num_gen;
        const hmac_dbrg_self_test_expected *Expected;
} hmac_dbrg_self_test;

#include <stdio.h>
int do_hmac_dbrg_self_tests(const hmac_dbrg_self_test *all_tests, unsigned int num_tests);

#endif /* HMAC_DRBG_SELF_TESTS */


#endif /* __HMAC_DRBG_TESTS_H__ */
