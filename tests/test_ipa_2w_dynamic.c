#include "secp256k1_mpt.h"
#include "test_utils.h"

#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SCALAR_SIZE 32

extern int secp256k1_bulletproof_run_ipa_prover_2w_dynamic(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const unsigned char *a_vec,
    const unsigned char *b_vec,
    size_t n,
    const unsigned char ipa_transcript_id[SCALAR_SIZE],
    const unsigned char ux_scalar[SCALAR_SIZE],
    secp256k1_pubkey *L_out,
    secp256k1_pubkey *R_out,
    size_t max_rounds,
    size_t *rounds_out,
    unsigned char a_final[SCALAR_SIZE],
    unsigned char b_final[SCALAR_SIZE]);

extern int ipa_verify_explicit_2w_dynamic(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L_vec,
    const secp256k1_pubkey *R_vec,
    size_t n,
    const unsigned char a_final[SCALAR_SIZE],
    const unsigned char b_final[SCALAR_SIZE],
    const unsigned char ux[SCALAR_SIZE],
    const unsigned char ipa_transcript_id[SCALAR_SIZE]);

extern int secp256k1_bulletproof_run_ipa_prover(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *U,
    secp256k1_pubkey *G_vec,
    secp256k1_pubkey *H_vec,
    unsigned char *a_vec,
    unsigned char *b_vec,
    size_t n,
    const unsigned char ipa_transcript_id[SCALAR_SIZE],
    const unsigned char ux_scalar[SCALAR_SIZE],
    secp256k1_pubkey *L_out,
    secp256k1_pubkey *R_out,
    size_t max_rounds,
    size_t *rounds_out,
    unsigned char a_final[SCALAR_SIZE],
    unsigned char b_final[SCALAR_SIZE]);

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
rounds_2w_dynamic(size_t n)
{
    size_t r = 0;
    while (n > 1)
    {
        n = (n + 1) / 2;
        ++r;
    }
    return r;
}

static int
is_power_of_two(size_t n)
{
    return n != 0 && (n & (n - 1)) == 0;
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
    static const unsigned char tag[] = "IPA_2W_DYNAMIC_TEST";
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

        if (!scalar_is_zero_local(ai))
        {
            tmp = G[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, ai))
                return 0;
            if (!add_term_local(ctx, P, &inited, &tmp))
                return 0;
        }

        if (!scalar_is_zero_local(bi))
        {
            tmp = H[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, bi))
                return 0;
            if (!add_term_local(ctx, P, &inited, &tmp))
                return 0;
        }
    }

    unsigned char dot_ux[SCALAR_SIZE];
    secp256k1_mpt_scalar_mul(dot_ux, dot, ux);

    if (!scalar_is_zero_local(dot_ux))
    {
        tmp = *U;
        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, dot_ux))
            return 0;
        if (!add_term_local(ctx, P, &inited, &tmp))
            return 0;
    }

    return inited;
}

static int
pubkey_equal_ser(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *a,
    const secp256k1_pubkey *b)
{
    unsigned char sa[33], sb[33];
    size_t la = sizeof(sa), lb = sizeof(sb);

    if (!secp256k1_ec_pubkey_serialize(
            ctx, sa, &la, a, SECP256K1_EC_COMPRESSED))
        return 0;
    if (!secp256k1_ec_pubkey_serialize(
            ctx, sb, &lb, b, SECP256K1_EC_COMPRESSED))
        return 0;

    return la == lb && memcmp(sa, sb, la) == 0;
}

static int
run_case(secp256k1_context *ctx, size_t n)
{
    const size_t rounds = rounds_2w_dynamic(n);

    secp256k1_pubkey *G = NULL, *H = NULL;
    secp256k1_pubkey *L = NULL, *R = NULL;
    unsigned char *a = NULL, *b = NULL;

    secp256k1_pubkey U, P;
    unsigned char dot[SCALAR_SIZE];
    unsigned char ux[SCALAR_SIZE];
    unsigned char transcript[SCALAR_SIZE];
    unsigned char a_final[SCALAR_SIZE];
    unsigned char b_final[SCALAR_SIZE];

    size_t rounds_out = 0;
    int ok = 0;

    printf("[2W-DYN IPA] n=%zu, expected rounds=%zu\n", n, rounds);

    G = (secp256k1_pubkey *)malloc(n * sizeof(*G));
    H = (secp256k1_pubkey *)malloc(n * sizeof(*H));
    a = (unsigned char *)malloc(n * SCALAR_SIZE);
    b = (unsigned char *)malloc(n * SCALAR_SIZE);

    if (rounds > 0)
    {
        L = (secp256k1_pubkey *)malloc(rounds * sizeof(*L));
        R = (secp256k1_pubkey *)malloc(rounds * sizeof(*R));
    }

    if (!G || !H || !a || !b || (rounds > 0 && (!L || !R)))
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, G, n, (const unsigned char *)"IPA2W_G", 7))
        goto cleanup;
    if (!secp256k1_mpt_get_generator_vector(
            ctx, H, n, (const unsigned char *)"IPA2W_H", 7))
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

    if (!secp256k1_bulletproof_run_ipa_prover_2w_dynamic(
            ctx, &U, G, H, a, b, n, transcript, ux,
            L, R, rounds, &rounds_out, a_final, b_final))
        goto cleanup;

    if (rounds_out != rounds)
    {
        fprintf(
            stderr,
            "[2W-DYN IPA] n=%zu: rounds_out=%zu, expected=%zu\n",
            n, rounds_out, rounds);
        goto cleanup;
    }

    if (!ipa_verify_explicit_2w_dynamic(
            ctx, G, H, &U, &P, L, R, n,
            a_final, b_final, ux, transcript))
    {
        fprintf(stderr, "[2W-DYN IPA] n=%zu: valid proof rejected\n", n);
        goto cleanup;
    }

    /*
     * For exact powers of two, dynamic 2W should be algebraically identical to
     * the existing binary prover because no padding coordinate is ever added.
     */
    if (is_power_of_two(n) && n > 1)
    {
        secp256k1_pubkey *Gs = malloc(n * sizeof(*Gs));
        secp256k1_pubkey *Hs = malloc(n * sizeof(*Hs));
        unsigned char *as = malloc(n * SCALAR_SIZE);
        unsigned char *bs = malloc(n * SCALAR_SIZE);
        secp256k1_pubkey *Ls = malloc(rounds * sizeof(*Ls));
        secp256k1_pubkey *Rs = malloc(rounds * sizeof(*Rs));
        unsigned char afs[SCALAR_SIZE], bfs[SCALAR_SIZE];
        size_t rs_out = 0;

        if (!Gs || !Hs || !as || !bs || !Ls || !Rs)
        {
            free(Gs); free(Hs); free(as); free(bs); free(Ls); free(Rs);
            goto cleanup;
        }

        memcpy(Gs, G, n * sizeof(*Gs));
        memcpy(Hs, H, n * sizeof(*Hs));
        memcpy(as, a, n * SCALAR_SIZE);
        memcpy(bs, b, n * SCALAR_SIZE);

        int std_ok = secp256k1_bulletproof_run_ipa_prover(
            ctx, &U, Gs, Hs, as, bs, n, transcript, ux,
            Ls, Rs, rounds, &rs_out, afs, bfs);

        if (!std_ok || rs_out != rounds ||
            memcmp(afs, a_final, SCALAR_SIZE) != 0 ||
            memcmp(bfs, b_final, SCALAR_SIZE) != 0)
        {
            fprintf(
                stderr,
                "[2W-DYN IPA] n=%zu: differs from standard binary final scalars\n",
                n);
            free(Gs); free(Hs); free(as); free(bs); free(Ls); free(Rs);
            goto cleanup;
        }

        for (size_t r = 0; r < rounds; ++r)
        {
            if (!pubkey_equal_ser(ctx, &Ls[r], &L[r]) ||
                !pubkey_equal_ser(ctx, &Rs[r], &R[r]))
            {
                fprintf(
                    stderr,
                    "[2W-DYN IPA] n=%zu: differs from standard binary at round %zu\n",
                    n, r);
                free(Gs); free(Hs); free(as); free(bs); free(Ls); free(Rs);
                goto cleanup;
            }
        }

        free(Gs); free(Hs); free(as); free(bs); free(Ls); free(Rs);
    }

    /* Tamper final scalar; verification must fail. */
    {
        unsigned char saved[SCALAR_SIZE];
        unsigned char one[SCALAR_SIZE] = {0};
        one[SCALAR_SIZE - 1] = 1;

        memcpy(saved, a_final, SCALAR_SIZE);
        secp256k1_mpt_scalar_add(a_final, a_final, one);

        if (ipa_verify_explicit_2w_dynamic(
                ctx, G, H, &U, &P, L, R, n,
                a_final, b_final, ux, transcript))
        {
            fprintf(
                stderr,
                "[2W-DYN IPA] n=%zu: tampered final scalar accepted\n",
                n);
            memcpy(a_final, saved, SCALAR_SIZE);
            goto cleanup;
        }

        memcpy(a_final, saved, SCALAR_SIZE);
    }

    /* Tamper the first L point for recursive cases. */
    if (rounds > 0)
    {
        secp256k1_pubkey saved = L[0];
        unsigned char two[SCALAR_SIZE] = {0};
        two[SCALAR_SIZE - 1] = 2;

        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &L[0], two))
            goto cleanup;

        if (ipa_verify_explicit_2w_dynamic(
                ctx, G, H, &U, &P, L, R, n,
                a_final, b_final, ux, transcript))
        {
            fprintf(stderr, "[2W-DYN IPA] n=%zu: tampered L accepted\n", n);
            L[0] = saved;
            goto cleanup;
        }

        L[0] = saved;
    }

    printf("[2W-DYN IPA] n=%zu PASSED\n", n);
    ok = 1;

cleanup:
    free(G);
    free(H);
    free(L);
    free(R);
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
     * Includes:
     *   exact powers of two, to compare byte-for-byte algebra with standard 2W;
     *   odd dimensions at several scales, to exercise local padding;
     *   dimensions immediately around binary boundaries.
     */
    static const size_t cases[] = {
        2, 3, 5, 7, 8,
        31, 32, 33,
        63, 64, 65,
        127, 128, 129,
        243, 244,
        255, 256, 257, 260
    };

    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i)
        EXPECT(run_case(ctx, cases[i]) == 1);

    secp256k1_context_destroy(ctx);

    printf("\n[SUCCESS] Dynamic 2W IPA tests passed!\n");
    return 0;
}
