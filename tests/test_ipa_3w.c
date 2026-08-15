#include "secp256k1_mpt.h"
#include "test_utils.h"

#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SCALAR_SIZE 32

/*
 * Experimental 3W IPA helpers from src/bulletproof_aggregated.c.
 *
 * For this test, remove `static` from the definitions of:
 *   secp256k1_bulletproof_run_ipa_prover_3w
 *   ipa_verify_explicit_3w
 *
 * A later cleanup can move these declarations to an internal-only header.
 */
extern int secp256k1_bulletproof_run_ipa_prover_3w(
    const secp256k1_context *ctx, const secp256k1_pubkey *U,
    const secp256k1_pubkey *G_vec, const secp256k1_pubkey *H_vec,
    const unsigned char *a_vec, const unsigned char *b_vec, size_t n,
    const unsigned char ipa_transcript_id[SCALAR_SIZE],
    const unsigned char ux_scalar[SCALAR_SIZE],
    secp256k1_pubkey *L1_out, secp256k1_pubkey *L2_out,
    secp256k1_pubkey *R1_out, secp256k1_pubkey *R2_out,
    size_t max_rounds, size_t *rounds_out,
    unsigned char a_final[SCALAR_SIZE],
    unsigned char b_final[SCALAR_SIZE]);

extern int ipa_verify_explicit_3w(
    const secp256k1_context *ctx, const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec, const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in, const secp256k1_pubkey *L1_vec,
    const secp256k1_pubkey *L2_vec, const secp256k1_pubkey *R1_vec,
    const secp256k1_pubkey *R2_vec, size_t n,
    const unsigned char a_final[SCALAR_SIZE],
    const unsigned char b_final[SCALAR_SIZE],
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char ipa_transcript_id[SCALAR_SIZE]);

extern int derive_ipa_binding_challenge(
    const secp256k1_context *ctx, unsigned char *ux_out,
    const unsigned char *commit_inp_32, const unsigned char *dot_32);

extern int secp256k1_bulletproof_ipa_dot(
    const secp256k1_context *ctx, unsigned char *out,
    const unsigned char *a, const unsigned char *b, size_t n);

static int
scalar_is_zero(unsigned char const s[SCALAR_SIZE])
{
    unsigned char z[SCALAR_SIZE] = {0};
    return memcmp(s, z, SCALAR_SIZE) == 0;
}

static int
add_term(
    const secp256k1_context *ctx,
    secp256k1_pubkey *acc,
    int *acc_inited,
    const secp256k1_pubkey *term)
{
    if (!*acc_inited)
    {
        *acc = *term;
        *acc_inited = 1;
        return 1;
    }

    secp256k1_pubkey sum;
    const secp256k1_pubkey *pts[2] = {acc, term};
    if (!secp256k1_ec_pubkey_combine(ctx, &sum, pts, 2))
        return 0;

    *acc = sum;
    return 1;
}

/* Number of dynamic-padding 3W rounds required to reach length 1. */
static size_t
rounds_3w(size_t n)
{
    size_t rounds = 0;
    while (n > 1)
    {
        n = (n + 2) / 3; /* ceil(n / 3) */
        ++rounds;
    }
    return rounds;
}

/*
 * Build a deterministic per-test transcript seed.
 * It need only be a stable 32-byte transcript identifier; the IPA round
 * challenges themselves are derived by the implementation.
 */
static void
make_transcript_id(unsigned char out[SCALAR_SIZE], size_t n)
{
    static const unsigned char tag[] = "IPA_3W_TEST";
    memset(out, 0, SCALAR_SIZE);
    memcpy(out, tag, sizeof(tag) - 1);

    /* Encode n in the final 8 bytes, big-endian. */
    uint64_t x = (uint64_t)n;
    for (int i = 0; i < 8; ++i)
    {
        out[SCALAR_SIZE - 1 - i] = (unsigned char)(x & 0xffu);
        x >>= 8;
    }
}

/*
 * Construct
 *
 *   P = <a,G> + <b,H> + ux*<a,b>*U.
 */
static int
build_initial_P(
    const secp256k1_context *ctx,
    secp256k1_pubkey *P,
    const secp256k1_pubkey *G,
    const secp256k1_pubkey *H,
    const secp256k1_pubkey *U,
    const unsigned char *a,
    const unsigned char *b,
    size_t n,
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char dot[SCALAR_SIZE])
{
    secp256k1_pubkey tmp;
    int inited = 0;

    for (size_t i = 0; i < n; ++i)
    {
        const unsigned char *ai = a + i * SCALAR_SIZE;
        const unsigned char *bi = b + i * SCALAR_SIZE;

        if (!scalar_is_zero(ai))
        {
            tmp = G[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, ai))
                return 0;
            if (!add_term(ctx, P, &inited, &tmp))
                return 0;
        }

        if (!scalar_is_zero(bi))
        {
            tmp = H[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, bi))
                return 0;
            if (!add_term(ctx, P, &inited, &tmp))
                return 0;
        }
    }

    unsigned char dot_ux[SCALAR_SIZE];
    secp256k1_mpt_scalar_mul(dot_ux, dot, ux);

    if (!scalar_is_zero(dot_ux))
    {
        tmp = *U;
        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, dot_ux))
            return 0;
        if (!add_term(ctx, P, &inited, &tmp))
            return 0;
    }

    return inited;
}

static int
run_case(secp256k1_context *ctx, size_t n)
{
    const size_t rounds = rounds_3w(n);

    secp256k1_pubkey *G = NULL;
    secp256k1_pubkey *H = NULL;
    secp256k1_pubkey *L1 = NULL;
    secp256k1_pubkey *L2 = NULL;
    secp256k1_pubkey *R1 = NULL;
    secp256k1_pubkey *R2 = NULL;
    unsigned char *a = NULL;
    unsigned char *b = NULL;

    secp256k1_pubkey U, P;
    unsigned char dot[SCALAR_SIZE];
    unsigned char ux[SCALAR_SIZE];
    unsigned char transcript[SCALAR_SIZE];
    unsigned char a_final[SCALAR_SIZE];
    unsigned char b_final[SCALAR_SIZE];
    size_t rounds_out = 0;
    int ok = 0;

    printf("[3W IPA] n=%zu, expected rounds=%zu\n", n, rounds);

    G = (secp256k1_pubkey *)malloc(n * sizeof(*G));
    H = (secp256k1_pubkey *)malloc(n * sizeof(*H));
    L1 = (secp256k1_pubkey *)malloc(rounds * sizeof(*L1));
    L2 = (secp256k1_pubkey *)malloc(rounds * sizeof(*L2));
    R1 = (secp256k1_pubkey *)malloc(rounds * sizeof(*R1));
    R2 = (secp256k1_pubkey *)malloc(rounds * sizeof(*R2));
    a = (unsigned char *)malloc(n * SCALAR_SIZE);
    b = (unsigned char *)malloc(n * SCALAR_SIZE);

    if (!G || !H || !L1 || !L2 || !R1 || !R2 || !a || !b)
        goto cleanup;

    /*
     * These labels are test-only. The statement is valid as long as prover
     * and verifier use the same generator vectors.
     */
    if (!secp256k1_mpt_get_generator_vector(
            ctx, G, n, (const unsigned char *)"IPA3W_G", 7))
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, H, n, (const unsigned char *)"IPA3W_H", 7))
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, &U, 1, (const unsigned char *)"BP_U", 4))
        goto cleanup;

    for (size_t i = 0; i < n; ++i)
    {
        random_scalar(ctx, a + i * SCALAR_SIZE);
        random_scalar(ctx, b + i * SCALAR_SIZE);
    }

    if (!secp256k1_bulletproof_ipa_dot(ctx, dot, a, b, n))
        goto cleanup;

    make_transcript_id(transcript, n);

    if (!derive_ipa_binding_challenge(ctx, ux, transcript, dot))
        goto cleanup;

    if (!build_initial_P(ctx, &P, G, H, &U, a, b, n, ux, dot))
        goto cleanup;

    if (!secp256k1_bulletproof_run_ipa_prover_3w(
            ctx, &U, G, H, a, b, n, transcript, ux,
            L1, L2, R1, R2, rounds, &rounds_out, a_final, b_final))
        goto cleanup;

    if (rounds_out != rounds)
    {
        fprintf(
            stderr,
            "[3W IPA] n=%zu: rounds_out=%zu, expected=%zu\n",
            n,
            rounds_out,
            rounds);
        goto cleanup;
    }

    if (!ipa_verify_explicit_3w(
            ctx, G, H, &U, &P, L1, L2, R1, R2, n,
            a_final, b_final, ux, transcript))
    {
        fprintf(stderr, "[3W IPA] n=%zu: valid proof rejected\n", n);
        goto cleanup;
    }

    /*
     * Negative test: alter L1[0]. Since the Fiat-Shamir challenge is bound
     * to L1,L2,R1,R2, the modified transcript/proof must fail verification.
     */
    {
        secp256k1_pubkey saved = L1[0];
        unsigned char two[SCALAR_SIZE] = {0};
        two[SCALAR_SIZE - 1] = 2;

        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &L1[0], two))
            goto cleanup;

        if (ipa_verify_explicit_3w(
                ctx, G, H, &U, &P, L1, L2, R1, R2, n,
                a_final, b_final, ux, transcript))
        {
            fprintf(stderr, "[3W IPA] n=%zu: tampered L1 accepted\n", n);
            L1[0] = saved;
            goto cleanup;
        }

        L1[0] = saved;
    }

    printf("[3W IPA] n=%zu PASSED\n", n);
    ok = 1;

cleanup:
    free(G);
    free(H);
    free(L1);
    free(L2);
    free(R1);
    free(R2);
    free(a);
    free(b);
    return ok;
}

int
main(void)
{
    secp256k1_context *ctx =
        secp256k1_context_create(
            SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    EXPECT(ctx != NULL);

    /*
     * Exact and dynamically padded lengths:
     *
     *   3   -> 1
     *   8   -> 9 -> 3 -> 1
     *   22  -> 24 -> 8 -> 9 -> 3 -> 1
     *   64  -> 66 -> 22 -> 24 -> 8 -> 9 -> 3 -> 1
     *   128 -> 129 -> 43 -> 45 -> 15 -> 5 -> 6 -> 2 -> 3 -> 1
     *
     * Each arrow from a padded length to the next reduced length is one 3W
     * recursion round. The test checks the resulting round count explicitly.
     */
    static const size_t cases[] = {3, 8, 22, 64, 128};

    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i)
        EXPECT(run_case(ctx, cases[i]) == 1);

    secp256k1_context_destroy(ctx);

    printf("\n[SUCCESS] Pure 3W IPA + dynamic-padding tests passed!\n");
    return 0;
}
