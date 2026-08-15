#include "secp256k1_mpt.h"
#include "test_utils.h"

#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SCALAR_SIZE 32
#define TERMINAL_MAX 3

extern int secp256k1_bulletproof_run_ipa_prover_3w_et(
    const secp256k1_context *ctx, const secp256k1_pubkey *U,
    const secp256k1_pubkey *G_vec, const secp256k1_pubkey *H_vec,
    const unsigned char *a_vec, const unsigned char *b_vec, size_t n,
    const unsigned char ipa_transcript_id[SCALAR_SIZE],
    const unsigned char ux_scalar[SCALAR_SIZE],
    secp256k1_pubkey *L1_out, secp256k1_pubkey *L2_out,
    secp256k1_pubkey *R1_out, secp256k1_pubkey *R2_out,
    size_t max_rounds, size_t *rounds_out,
    unsigned char a_terminal[TERMINAL_MAX * SCALAR_SIZE],
    unsigned char b_terminal[TERMINAL_MAX * SCALAR_SIZE],
    size_t *terminal_n_out);

extern int ipa_verify_explicit_3w_et(
    const secp256k1_context *ctx, const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec, const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L1_vec, const secp256k1_pubkey *L2_vec,
    const secp256k1_pubkey *R1_vec, const secp256k1_pubkey *R2_vec,
    size_t n,
    const unsigned char a_terminal[TERMINAL_MAX * SCALAR_SIZE],
    const unsigned char b_terminal[TERMINAL_MAX * SCALAR_SIZE],
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char ipa_transcript_id[SCALAR_SIZE]);

extern int derive_ipa_binding_challenge(
    const secp256k1_context *ctx, unsigned char *ux_out,
    const unsigned char *commit_inp_32, const unsigned char *dot_32);

extern int secp256k1_bulletproof_ipa_dot(
    const secp256k1_context *ctx, unsigned char *out,
    const unsigned char *a, const unsigned char *b, size_t n);

static size_t
rounds_3w_et(size_t n)
{
    size_t r = 0;
    while (n > 3)
    {
        n = (n + 2) / 3;
        ++r;
    }
    return r;
}

static size_t
terminal_len_3w_et(size_t n)
{
    while (n > 3)
        n = (n + 2) / 3;
    return n;
}

static int
scalar_is_zero(const unsigned char s[SCALAR_SIZE])
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

static void
make_transcript_id(unsigned char out[SCALAR_SIZE], size_t n)
{
    static const unsigned char tag[] = "IPA_3W_ET_TEST";
    memset(out, 0, SCALAR_SIZE);
    memcpy(out, tag, sizeof(tag) - 1);

    uint64_t x = (uint64_t)n;
    for (int i = 0; i < 8; ++i)
    {
        out[SCALAR_SIZE - 1 - i] = (unsigned char)(x & 0xffu);
        x >>= 8;
    }
}

/* P = <a,G> + <b,H> + ux*<a,b>*U. */
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
    const size_t rounds = rounds_3w_et(n);
    const size_t expected_terminal_n = terminal_len_3w_et(n);

    secp256k1_pubkey *G = NULL, *H = NULL;
    secp256k1_pubkey *L1 = NULL, *L2 = NULL, *R1 = NULL, *R2 = NULL;
    unsigned char *a = NULL, *b = NULL;

    secp256k1_pubkey U, P;
    unsigned char dot[SCALAR_SIZE];
    unsigned char ux[SCALAR_SIZE];
    unsigned char transcript[SCALAR_SIZE];
    unsigned char a_terminal[TERMINAL_MAX * SCALAR_SIZE];
    unsigned char b_terminal[TERMINAL_MAX * SCALAR_SIZE];
    size_t rounds_out = 0;
    size_t terminal_n_out = 0;
    int ok = 0;

    printf(
        "[3W-ET IPA] n=%zu, rounds=%zu, terminal_n=%zu\n",
        n, rounds, expected_terminal_n);

    G = (secp256k1_pubkey *)malloc(n * sizeof(*G));
    H = (secp256k1_pubkey *)malloc(n * sizeof(*H));
    a = (unsigned char *)malloc(n * SCALAR_SIZE);
    b = (unsigned char *)malloc(n * SCALAR_SIZE);

    if (rounds > 0)
    {
        L1 = (secp256k1_pubkey *)malloc(rounds * sizeof(*L1));
        L2 = (secp256k1_pubkey *)malloc(rounds * sizeof(*L2));
        R1 = (secp256k1_pubkey *)malloc(rounds * sizeof(*R1));
        R2 = (secp256k1_pubkey *)malloc(rounds * sizeof(*R2));
    }

    if (!G || !H || !a || !b ||
        (rounds > 0 && (!L1 || !L2 || !R1 || !R2)))
        goto cleanup;

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

    if (!secp256k1_bulletproof_run_ipa_prover_3w_et(
            ctx, &U, G, H, a, b, n, transcript, ux,
            L1, L2, R1, R2, rounds, &rounds_out,
            a_terminal, b_terminal, &terminal_n_out))
        goto cleanup;

    if (rounds_out != rounds || terminal_n_out != expected_terminal_n)
    {
        fprintf(
            stderr,
            "[3W-ET IPA] n=%zu: got rounds=%zu terminal=%zu; expected %zu/%zu\n",
            n, rounds_out, terminal_n_out, rounds, expected_terminal_n);
        goto cleanup;
    }

    if (!ipa_verify_explicit_3w_et(
            ctx, G, H, &U, &P, L1, L2, R1, R2, n,
            a_terminal, b_terminal, ux, transcript))
    {
        fprintf(stderr, "[3W-ET IPA] n=%zu: valid proof rejected\n", n);
        goto cleanup;
    }

    /* Tamper a terminal scalar; verification must fail. */
    {
        unsigned char saved[SCALAR_SIZE];
        unsigned char one[SCALAR_SIZE] = {0};
        one[SCALAR_SIZE - 1] = 1;

        memcpy(saved, a_terminal, SCALAR_SIZE);
        secp256k1_mpt_scalar_add(a_terminal, a_terminal, one);

        if (ipa_verify_explicit_3w_et(
                ctx, G, H, &U, &P, L1, L2, R1, R2, n,
                a_terminal, b_terminal, ux, transcript))
        {
            fprintf(
                stderr,
                "[3W-ET IPA] n=%zu: tampered terminal scalar accepted\n",
                n);
            memcpy(a_terminal, saved, SCALAR_SIZE);
            goto cleanup;
        }

        memcpy(a_terminal, saved, SCALAR_SIZE);
    }

    /* For recursive cases, tamper L1[0] as well. */
    if (rounds > 0)
    {
        secp256k1_pubkey saved = L1[0];
        unsigned char two[SCALAR_SIZE] = {0};
        two[SCALAR_SIZE - 1] = 2;

        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &L1[0], two))
            goto cleanup;

        if (ipa_verify_explicit_3w_et(
                ctx, G, H, &U, &P, L1, L2, R1, R2, n,
                a_terminal, b_terminal, ux, transcript))
        {
            fprintf(stderr, "[3W-ET IPA] n=%zu: tampered L1 accepted\n", n);
            L1[0] = saved;
            goto cleanup;
        }

        L1[0] = saved;
    }

    printf("[3W-ET IPA] n=%zu PASSED\n", n);
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
     * Includes both terminal sizes:
     *   2   -> ET(2)
     *   3   -> ET(3)
     *   4   -> 2 -> ET(2)
     *   5   -> 2 -> ET(2)
     *   8   -> 3 -> ET(3)
     *   22  -> 8 -> 3 -> ET(3)
     *   64  -> 22 -> 8 -> 3 -> ET(3)
     *   128 -> 43 -> 15 -> 5 -> 2 -> ET(2)
     *   243 -> 81 -> 27 -> 9 -> 3 -> ET(3)
     *   244 -> 82 -> 28 -> 10 -> 4 -> 2 -> ET(2)
     */
    static const size_t cases[] = {
        2, 3, 4, 5, 8, 22, 64, 128, 243, 244
    };

    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i)
        EXPECT(run_case(ctx, cases[i]) == 1);

    secp256k1_context_destroy(ctx);

    printf("\n[SUCCESS] 3W IPA early-termination tests passed!\n");
    return 0;
}
