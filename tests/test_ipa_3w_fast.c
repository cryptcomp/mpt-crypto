#include "secp256k1_mpt.h"
#include "test_utils.h"

#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SCALAR_SIZE 32
#define TERMINAL_MAX 3

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
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L1_vec, const secp256k1_pubkey *L2_vec,
    const secp256k1_pubkey *R1_vec, const secp256k1_pubkey *R2_vec,
    size_t n,
    const unsigned char a_final[SCALAR_SIZE],
    const unsigned char b_final[SCALAR_SIZE],
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char ipa_transcript_id[SCALAR_SIZE]);

extern int ipa_verify_explicit_3w_fast(
    const secp256k1_context *ctx, const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec, const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L1_vec, const secp256k1_pubkey *L2_vec,
    const secp256k1_pubkey *R1_vec, const secp256k1_pubkey *R2_vec,
    size_t n,
    const unsigned char a_final[SCALAR_SIZE],
    const unsigned char b_final[SCALAR_SIZE],
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char ipa_transcript_id[SCALAR_SIZE]);

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

extern int ipa_verify_explicit_3w_et_fast(
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
rounds_3w(size_t n)
{
    size_t r = 0;
    while (n > 1)
    {
        n = (n + 2) / 3;
        ++r;
    }
    return r;
}

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
scalar_is_zero_local(const unsigned char s[SCALAR_SIZE])
{
    unsigned char z[SCALAR_SIZE] = {0};
    return memcmp(s, z, SCALAR_SIZE) == 0;
}

static int
add_term_local(
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
    static const unsigned char tag[] = "IPA_3W_FAST_TEST";
    uint64_t x = (uint64_t)n;

    memset(out, 0, SCALAR_SIZE);
    memcpy(out, tag, sizeof(tag) - 1);

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

        if (!scalar_is_zero_local(ai))
        {
            tmp = G[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, ai) ||
                !add_term_local(ctx, P, &inited, &tmp))
                return 0;
        }

        if (!scalar_is_zero_local(bi))
        {
            tmp = H[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, bi) ||
                !add_term_local(ctx, P, &inited, &tmp))
                return 0;
        }
    }

    {
        unsigned char dot_ux[SCALAR_SIZE];
        secp256k1_mpt_scalar_mul(dot_ux, dot, ux);

        if (!scalar_is_zero_local(dot_ux))
        {
            tmp = *U;
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, dot_ux) ||
                !add_term_local(ctx, P, &inited, &tmp))
                return 0;
        }
    }

    return inited;
}

static int
run_case(secp256k1_context *ctx, size_t n)
{
    const size_t rp = rounds_3w(n);
    const size_t re = rounds_3w_et(n);
    const size_t te = terminal_len_3w_et(n);

    secp256k1_pubkey *G = NULL, *H = NULL;
    unsigned char *a = NULL, *b = NULL;

    secp256k1_pubkey *pL1 = NULL, *pL2 = NULL, *pR1 = NULL, *pR2 = NULL;
    secp256k1_pubkey *eL1 = NULL, *eL2 = NULL, *eR1 = NULL, *eR2 = NULL;

    secp256k1_pubkey U, P;
    unsigned char dot[SCALAR_SIZE];
    unsigned char ux[SCALAR_SIZE];
    unsigned char transcript[SCALAR_SIZE];

    unsigned char af[SCALAR_SIZE], bf[SCALAR_SIZE];
    unsigned char at[TERMINAL_MAX * SCALAR_SIZE];
    unsigned char bt[TERMINAL_MAX * SCALAR_SIZE];

    size_t rounds_out = 0;
    size_t terminal_n_out = 0;
    int ok = 0;

    printf(
        "[3W-FAST] n=%zu pure_rounds=%zu et_rounds=%zu terminal=%zu\n",
        n, rp, re, te);

    G = malloc(n * sizeof(*G));
    H = malloc(n * sizeof(*H));
    a = malloc(n * SCALAR_SIZE);
    b = malloc(n * SCALAR_SIZE);

    if (rp > 0)
    {
        pL1 = malloc(rp * sizeof(*pL1));
        pL2 = malloc(rp * sizeof(*pL2));
        pR1 = malloc(rp * sizeof(*pR1));
        pR2 = malloc(rp * sizeof(*pR2));
    }

    if (re > 0)
    {
        eL1 = malloc(re * sizeof(*eL1));
        eL2 = malloc(re * sizeof(*eL2));
        eR1 = malloc(re * sizeof(*eR1));
        eR2 = malloc(re * sizeof(*eR2));
    }

    if (!G || !H || !a || !b ||
        (rp > 0 && (!pL1 || !pL2 || !pR1 || !pR2)) ||
        (re > 0 && (!eL1 || !eL2 || !eR1 || !eR2)))
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

    /* -------- Pure 3W: same proof, slow and fast verifier -------- */
    if (!secp256k1_bulletproof_run_ipa_prover_3w(
            ctx, &U, G, H, a, b, n, transcript, ux,
            pL1, pL2, pR1, pR2, rp, &rounds_out, af, bf) ||
        rounds_out != rp)
        goto cleanup;

    if (!ipa_verify_explicit_3w(
            ctx, G, H, &U, &P,
            pL1, pL2, pR1, pR2, n,
            af, bf, ux, transcript))
    {
        fprintf(stderr, "[3W-FAST] n=%zu pure slow rejected valid proof\n", n);
        goto cleanup;
    }

    if (!ipa_verify_explicit_3w_fast(
            ctx, G, H, &U, &P,
            pL1, pL2, pR1, pR2, n,
            af, bf, ux, transcript))
    {
        fprintf(stderr, "[3W-FAST] n=%zu pure fast rejected valid proof\n", n);
        goto cleanup;
    }

    /* Pure-proof tamper must be rejected by both verifier methods. */
    if (rp > 0)
    {
        secp256k1_pubkey saved = pL1[0];
        unsigned char two[SCALAR_SIZE] = {0};
        two[SCALAR_SIZE - 1] = 2;

        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &pL1[0], two))
            goto cleanup;

        if (ipa_verify_explicit_3w(
                ctx, G, H, &U, &P,
                pL1, pL2, pR1, pR2, n,
                af, bf, ux, transcript) ||
            ipa_verify_explicit_3w_fast(
                ctx, G, H, &U, &P,
                pL1, pL2, pR1, pR2, n,
                af, bf, ux, transcript))
        {
            fprintf(stderr, "[3W-FAST] n=%zu pure tamper accepted\n", n);
            pL1[0] = saved;
            goto cleanup;
        }

        pL1[0] = saved;
    }

    /* -------- 3W-ET: same proof, slow and fast verifier -------- */
    if (!secp256k1_bulletproof_run_ipa_prover_3w_et(
            ctx, &U, G, H, a, b, n, transcript, ux,
            eL1, eL2, eR1, eR2, re, &rounds_out,
            at, bt, &terminal_n_out) ||
        rounds_out != re || terminal_n_out != te)
        goto cleanup;

    if (!ipa_verify_explicit_3w_et(
            ctx, G, H, &U, &P,
            eL1, eL2, eR1, eR2, n,
            at, bt, ux, transcript))
    {
        fprintf(stderr, "[3W-FAST] n=%zu ET slow rejected valid proof\n", n);
        goto cleanup;
    }

    if (!ipa_verify_explicit_3w_et_fast(
            ctx, G, H, &U, &P,
            eL1, eL2, eR1, eR2, n,
            at, bt, ux, transcript))
    {
        fprintf(stderr, "[3W-FAST] n=%zu ET fast rejected valid proof\n", n);
        goto cleanup;
    }

    /* Terminal-scalar tamper must be rejected by both ET verifiers. */
    {
        unsigned char saved[SCALAR_SIZE];
        unsigned char one[SCALAR_SIZE] = {0};
        one[SCALAR_SIZE - 1] = 1;

        memcpy(saved, at, SCALAR_SIZE);
        secp256k1_mpt_scalar_add(at, at, one);

        if (ipa_verify_explicit_3w_et(
                ctx, G, H, &U, &P,
                eL1, eL2, eR1, eR2, n,
                at, bt, ux, transcript) ||
            ipa_verify_explicit_3w_et_fast(
                ctx, G, H, &U, &P,
                eL1, eL2, eR1, eR2, n,
                at, bt, ux, transcript))
        {
            fprintf(stderr, "[3W-FAST] n=%zu ET scalar tamper accepted\n", n);
            memcpy(at, saved, SCALAR_SIZE);
            goto cleanup;
        }

        memcpy(at, saved, SCALAR_SIZE);
    }

    if (re > 0)
    {
        secp256k1_pubkey saved = eL1[0];
        unsigned char two[SCALAR_SIZE] = {0};
        two[SCALAR_SIZE - 1] = 2;

        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &eL1[0], two))
            goto cleanup;

        if (ipa_verify_explicit_3w_et(
                ctx, G, H, &U, &P,
                eL1, eL2, eR1, eR2, n,
                at, bt, ux, transcript) ||
            ipa_verify_explicit_3w_et_fast(
                ctx, G, H, &U, &P,
                eL1, eL2, eR1, eR2, n,
                at, bt, ux, transcript))
        {
            fprintf(stderr, "[3W-FAST] n=%zu ET point tamper accepted\n", n);
            eL1[0] = saved;
            goto cleanup;
        }

        eL1[0] = saved;
    }

    printf("[3W-FAST] n=%zu PASSED (pure+ET slow/fast agree)\n", n);
    ok = 1;

cleanup:
    free(G);
    free(H);
    free(a);
    free(b);

    free(pL1);
    free(pL2);
    free(pR1);
    free(pR2);

    free(eL1);
    free(eL2);
    free(eR1);
    free(eR2);

    return ok;
}

int
main(void)
{
    secp256k1_context *ctx =
        secp256k1_context_create(
            SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    EXPECT(ctx != NULL);

    static const size_t cases[] = {
        2, 3, 4, 5, 8, 22,
        55, 63, 64, 65,
        127, 128, 129,
        243, 244,
        255, 256, 257, 260
    };

    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i)
        EXPECT(run_case(ctx, cases[i]) == 1);

    secp256k1_context_destroy(ctx);

    printf("\n[SUCCESS] Optimized 3W verifier tests passed!\n");
    return 0;
}
