#include "secp256k1_mpt.h"
#include "test_utils.h"

#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SCALAR_SIZE 32
#define TERMINAL_MAX 3

extern int secp256k1_bulletproof_ipa_hybrid_v1_schedule(
    size_t n, size_t k3,
    size_t *r3_out, size_t *r2_out, size_t *terminal_n_out);

extern int secp256k1_bulletproof_run_ipa_prover_hybrid_v1(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const unsigned char *a_vec,
    const unsigned char *b_vec,
    size_t n,
    size_t k3,
    const unsigned char ipa_transcript_id[SCALAR_SIZE],
    const unsigned char ux_scalar[SCALAR_SIZE],
    secp256k1_pubkey *L1_3w_out,
    secp256k1_pubkey *L2_3w_out,
    secp256k1_pubkey *R1_3w_out,
    secp256k1_pubkey *R2_3w_out,
    size_t max_3w_rounds,
    size_t *r3_out,
    secp256k1_pubkey *L_2w_out,
    secp256k1_pubkey *R_2w_out,
    size_t max_2w_rounds,
    size_t *r2_out,
    unsigned char a_terminal[TERMINAL_MAX * SCALAR_SIZE],
    unsigned char b_terminal[TERMINAL_MAX * SCALAR_SIZE],
    size_t *terminal_n_out);

extern int ipa_verify_explicit_hybrid_v1(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    size_t n,
    size_t k3,
    const secp256k1_pubkey *L1_3w_vec,
    const secp256k1_pubkey *L2_3w_vec,
    const secp256k1_pubkey *R1_3w_vec,
    const secp256k1_pubkey *R2_3w_vec,
    const secp256k1_pubkey *L_2w_vec,
    const secp256k1_pubkey *R_2w_vec,
    const unsigned char a_terminal[TERMINAL_MAX * SCALAR_SIZE],
    const unsigned char b_terminal[TERMINAL_MAX * SCALAR_SIZE],
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char ipa_transcript_id[SCALAR_SIZE]);

extern int derive_ipa_binding_challenge(
    const secp256k1_context *ctx,
    unsigned char *ux_out,
    const unsigned char *commit_inp_32,
    const unsigned char *dot_32);

extern int secp256k1_bulletproof_ipa_dot(
    const secp256k1_context *ctx,
    unsigned char *out,
    const unsigned char *a,
    const unsigned char *b,
    size_t n);

static size_t
max_k3_local(size_t n)
{
    size_t r = 0;
    while (n > 3)
    {
        n = (n + 2) / 3;
        ++r;
    }
    return r;
}

static void
schedule_local(
    size_t n, size_t k3,
    size_t *r3, size_t *r2, size_t *terminal)
{
    size_t cur = n;
    size_t b = 0;

    for (size_t i = 0; i < k3; ++i)
        cur = (cur + 2) / 3;

    while (cur > 3)
    {
        cur = (cur + 1) / 2;
        ++b;
    }

    *r3 = k3;
    *r2 = b;
    *terminal = cur;
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

    {
        secp256k1_pubkey sum;
        const secp256k1_pubkey *pts[2] = {acc, term};

        if (!secp256k1_ec_pubkey_combine(ctx, &sum, pts, 2))
            return 0;

        *acc = sum;
        return 1;
    }
}

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

static void
make_transcript_id(unsigned char out[SCALAR_SIZE], size_t n)
{
    static const unsigned char tag[] = "IPA_HYBRID_V1_TEST";
    uint64_t x = (uint64_t)n;

    memset(out, 0, SCALAR_SIZE);
    memcpy(out, tag, sizeof(tag) - 1);

    for (int i = 0; i < 8; ++i)
    {
        out[SCALAR_SIZE - 1 - i] = (unsigned char)(x & 0xffu);
        x >>= 8;
    }
}

static int
verify_current(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G,
    const secp256k1_pubkey *H,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P,
    size_t n,
    size_t k3,
    const secp256k1_pubkey *L1,
    const secp256k1_pubkey *L2,
    const secp256k1_pubkey *R1,
    const secp256k1_pubkey *R2,
    const secp256k1_pubkey *Lb,
    const secp256k1_pubkey *Rb,
    const unsigned char at[TERMINAL_MAX * SCALAR_SIZE],
    const unsigned char bt[TERMINAL_MAX * SCALAR_SIZE],
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char transcript[SCALAR_SIZE])
{
    return ipa_verify_explicit_hybrid_v1(
        ctx, G, H, U, P, n, k3,
        L1, L2, R1, R2, Lb, Rb,
        at, bt, ux, transcript);
}

static int
run_schedule_case(secp256k1_context *ctx, size_t n, size_t k3)
{
    const size_t max3 = max_k3_local(n);
    size_t er3 = 0, er2 = 0, et = 0;
    size_t sr3 = 0, sr2 = 0, st = 0;

    secp256k1_pubkey *G = NULL, *H = NULL;
    unsigned char *a = NULL, *b = NULL;

    secp256k1_pubkey *L1 = NULL, *L2 = NULL, *R1 = NULL, *R2 = NULL;
    secp256k1_pubkey *Lb = NULL, *Rb = NULL;

    secp256k1_pubkey U, P;
    unsigned char dot[SCALAR_SIZE] = {0};
    unsigned char ux[SCALAR_SIZE] = {0};
    unsigned char transcript[SCALAR_SIZE] = {0};
    unsigned char at[TERMINAL_MAX * SCALAR_SIZE] = {0};
    unsigned char bt[TERMINAL_MAX * SCALAR_SIZE] = {0};

    size_t pr3 = 0, pr2 = 0, pt = 0;
    int ok = 0;

    if (k3 > max3)
        return 0;

    schedule_local(n, k3, &er3, &er2, &et);

    if (!secp256k1_bulletproof_ipa_hybrid_v1_schedule(
            n, k3, &sr3, &sr2, &st) ||
        sr3 != er3 || sr2 != er2 || st != et)
    {
        fprintf(stderr, "schedule helper mismatch n=%zu H%zu\n", n, k3);
        return 0;
    }

    G = malloc(n * sizeof(*G));
    H = malloc(n * sizeof(*H));
    a = malloc(n * SCALAR_SIZE);
    b = malloc(n * SCALAR_SIZE);

    L1 = calloc(er3 ? er3 : 1, sizeof(*L1));
    L2 = calloc(er3 ? er3 : 1, sizeof(*L2));
    R1 = calloc(er3 ? er3 : 1, sizeof(*R1));
    R2 = calloc(er3 ? er3 : 1, sizeof(*R2));

    Lb = calloc(er2 ? er2 : 1, sizeof(*Lb));
    Rb = calloc(er2 ? er2 : 1, sizeof(*Rb));

    if (!G || !H || !a || !b ||
        !L1 || !L2 || !R1 || !R2 || !Lb || !Rb)
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, G, n,
            (const unsigned char *)"HYB1_TEST_G", 11))
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, H, n,
            (const unsigned char *)"HYB1_TEST_H", 11))
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, &U, 1,
            (const unsigned char *)"HYB1_TEST_U", 11))
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

    if (!secp256k1_bulletproof_run_ipa_prover_hybrid_v1(
            ctx, &U, G, H, a, b, n, k3, transcript, ux,
            er3 ? L1 : NULL, er3 ? L2 : NULL,
            er3 ? R1 : NULL, er3 ? R2 : NULL,
            er3, &pr3,
            er2 ? Lb : NULL, er2 ? Rb : NULL,
            er2, &pr2,
            at, bt, &pt))
    {
        fprintf(stderr, "prover failed n=%zu H%zu\n", n, k3);
        goto cleanup;
    }

    if (pr3 != er3 || pr2 != er2 || pt != et)
    {
        fprintf(
            stderr,
            "prover schedule mismatch n=%zu H%zu: "
            "got (%zu,%zu,t%zu), expected (%zu,%zu,t%zu)\n",
            n, k3, pr3, pr2, pt, er3, er2, et);
        goto cleanup;
    }

    if (!verify_current(
            ctx, G, H, &U, &P, n, k3,
            er3 ? L1 : NULL, er3 ? L2 : NULL,
            er3 ? R1 : NULL, er3 ? R2 : NULL,
            er2 ? Lb : NULL, er2 ? Rb : NULL,
            at, bt, ux, transcript))
    {
        fprintf(stderr, "valid proof rejected n=%zu H%zu\n", n, k3);
        goto cleanup;
    }

    /*
     * The Hybrid-v1 seed affects Fiat-Shamir round challenges.
     * With zero IPA rounds (n <= 3), there is no round challenge,
     * so ipa_transcript_id alone cannot affect the terminal check.
     */
    if (er3 + er2 > 0)
    {
        unsigned char bad_transcript[SCALAR_SIZE];
        memcpy(bad_transcript, transcript, sizeof(bad_transcript));
        bad_transcript[0] ^= 0x01u;

        if (verify_current(
                ctx, G, H, &U, &P, n, k3,
                er3 ? L1 : NULL, er3 ? L2 : NULL,
                er3 ? R1 : NULL, er3 ? R2 : NULL,
                er2 ? Lb : NULL, er2 ? Rb : NULL,
                at, bt, ux, bad_transcript))
        {
            fprintf(stderr, "transcript tamper accepted n=%zu H%zu\n", n, k3);
            goto cleanup;
        }
    }

    /* Terminal scalar tamper. */
    {
        unsigned char saved[SCALAR_SIZE];
        unsigned char one[SCALAR_SIZE] = {0};
        one[SCALAR_SIZE - 1] = 1;
        memcpy(saved, at, SCALAR_SIZE);

        secp256k1_mpt_scalar_add(at, at, one);

        if (verify_current(
                ctx, G, H, &U, &P, n, k3,
                er3 ? L1 : NULL, er3 ? L2 : NULL,
                er3 ? R1 : NULL, er3 ? R2 : NULL,
                er2 ? Lb : NULL, er2 ? Rb : NULL,
                at, bt, ux, transcript))
        {
            fprintf(stderr, "terminal tamper accepted n=%zu H%zu\n", n, k3);
            memcpy(at, saved, SCALAR_SIZE);
            goto cleanup;
        }

        memcpy(at, saved, SCALAR_SIZE);
    }

    /* First 3W commitment tamper if the schedule contains a 3W round. */
    if (er3 > 0)
    {
        secp256k1_pubkey saved = L1[0];
        unsigned char two[SCALAR_SIZE] = {0};
        two[SCALAR_SIZE - 1] = 2;

        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &L1[0], two))
            goto cleanup;

        if (verify_current(
                ctx, G, H, &U, &P, n, k3,
                L1, L2, R1, R2,
                er2 ? Lb : NULL, er2 ? Rb : NULL,
                at, bt, ux, transcript))
        {
            fprintf(stderr, "3W point tamper accepted n=%zu H%zu\n", n, k3);
            L1[0] = saved;
            goto cleanup;
        }

        L1[0] = saved;
    }

    /* First 2W commitment tamper if the schedule contains a 2W round. */
    if (er2 > 0)
    {
        secp256k1_pubkey saved = Lb[0];
        unsigned char two[SCALAR_SIZE] = {0};
        two[SCALAR_SIZE - 1] = 2;

        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &Lb[0], two))
            goto cleanup;

        if (verify_current(
                ctx, G, H, &U, &P, n, k3,
                er3 ? L1 : NULL, er3 ? L2 : NULL,
                er3 ? R1 : NULL, er3 ? R2 : NULL,
                Lb, Rb, at, bt, ux, transcript))
        {
            fprintf(stderr, "2W point tamper accepted n=%zu H%zu\n", n, k3);
            Lb[0] = saved;
            goto cleanup;
        }

        Lb[0] = saved;
    }

    {
        const size_t bytes =
            132 * er3 + 66 * er2 + 64 * et;

        printf(
            "[HYB-V1] n=%zu H%zu: 3W=%zu 2W=%zu terminal=%zu "
            "IPA-bytes=%zu PASSED\n",
            n, k3, er3, er2, et, bytes);
    }

    ok = 1;

cleanup:
    free(G);
    free(H);
    free(a);
    free(b);

    free(L1);
    free(L2);
    free(R1);
    free(R2);
    free(Lb);
    free(Rb);

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
        1, 2, 3, 4, 5, 8, 22,
        64, 65, 128, 129,
        243, 244, 256, 257
    };

    for (size_t c = 0; c < sizeof(cases) / sizeof(cases[0]); ++c)
    {
        const size_t n = cases[c];
        const size_t max3 = max_k3_local(n);

        for (size_t k3 = 0; k3 <= max3; ++k3)
            EXPECT(run_schedule_case(ctx, n, k3) == 1);

        /* Non-canonical prefix length must be rejected. */
        EXPECT(
            secp256k1_bulletproof_ipa_hybrid_v1_schedule(
                n, max3 + 1, NULL, NULL, NULL) == 0);
    }

    secp256k1_context_destroy(ctx);

    printf("\n[SUCCESS] Hybrid v1 reference prover/verifier tests passed!\n");
    return 0;
}
