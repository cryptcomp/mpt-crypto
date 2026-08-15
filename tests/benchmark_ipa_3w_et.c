/*
 * benchmark_ipa_3w.c
 *
 * Microbenchmark for the existing binary Bulletproof IPA versus the new
 * pure 3-way IPA with dynamic padding and termination at length 1.
 *
 * This benchmarks the IPA layer only. Generator derivation, witness creation,
 * the initial commitment P, and input reset copies for the binary prover are
 * outside the timed regions.
 *
 * Important interpretation:
 *   - The binary prover mutates its inputs, so its reset memcpy operations are
 *     deliberately performed before the timer starts.
 *   - The current 3W prover copies/allocates its working vectors internally,
 *     so those costs ARE included. Therefore these numbers compare the current
 *     implementations as they exist today, not an allocation-free idealization.
 *
 * Usage:
 *   ./tests/benchmark_ipa_3w
 *   ./tests/benchmark_ipa_3w 100 500
 *
 * argv[1] = prover iterations  (default 50)
 * argv[2] = verifier iterations (default 200)
 */

#define _GNU_SOURCE

#include "secp256k1_mpt.h"
#include "test_utils.h"

#include <secp256k1.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define SCALAR_SIZE 32
#define WARMUP_ITERS 10

/* Existing binary IPA prover. */
extern int secp256k1_bulletproof_run_ipa_prover(
    const secp256k1_context *ctx, const secp256k1_pubkey *U,
    secp256k1_pubkey *G_vec, secp256k1_pubkey *H_vec,
    unsigned char *a_vec, unsigned char *b_vec, size_t n,
    const unsigned char ipa_transcript_id[SCALAR_SIZE],
    const unsigned char ux_scalar[SCALAR_SIZE],
    secp256k1_pubkey *L_out, secp256k1_pubkey *R_out,
    size_t max_rounds, size_t *rounds_out,
    unsigned char a_final[SCALAR_SIZE],
    unsigned char b_final[SCALAR_SIZE]);

/* Expose this by removing `static` from its definition in
 * src/bulletproof_aggregated.c. */
extern int ipa_verify_explicit(
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

/* Pure 3W IPA helpers already exposed for test_ipa_3w.c. */
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
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L1_vec,
    const secp256k1_pubkey *L2_vec,
    const secp256k1_pubkey *R1_vec,
    const secp256k1_pubkey *R2_vec,
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
    unsigned char a_terminal[3 * SCALAR_SIZE],
    unsigned char b_terminal[3 * SCALAR_SIZE],
    size_t *terminal_n_out);

extern int ipa_verify_explicit_3w_et(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L1_vec,
    const secp256k1_pubkey *L2_vec,
    const secp256k1_pubkey *R1_vec,
    const secp256k1_pubkey *R2_vec,
    size_t n,
    const unsigned char a_terminal[3 * SCALAR_SIZE],
    const unsigned char b_terminal[3 * SCALAR_SIZE],
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

struct bench_stats
{
    double mean_ms;
    double median_ms;
    double min_ms;
    double p95_ms;
    double max_ms;
};

static uint64_t
now_ns(void)
{
    struct timespec ts;
#ifdef CLOCK_MONOTONIC_RAW
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &ts) != 0)
        abort();
#else
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
        abort();
#endif
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static int
cmp_double(const void *pa, const void *pb)
{
    const double a = *(const double *)pa;
    const double b = *(const double *)pb;
    return (a > b) - (a < b);
}

static struct bench_stats
summarize(double *samples, size_t n)
{
    struct bench_stats s = {0};
    double sum = 0.0;

    for (size_t i = 0; i < n; ++i)
        sum += samples[i];

    qsort(samples, n, sizeof(*samples), cmp_double);

    s.mean_ms = sum / (double)n;
    s.min_ms = samples[0];
    s.max_ms = samples[n - 1];

    if ((n & 1u) != 0)
        s.median_ms = samples[n / 2];
    else
        s.median_ms = 0.5 * (samples[n / 2 - 1] + samples[n / 2]);

    size_t p95_index = (95 * n + 99) / 100; /* ceil(0.95*n) */
    if (p95_index == 0)
        p95_index = 1;
    if (p95_index > n)
        p95_index = n;
    s.p95_ms = samples[p95_index - 1];

    return s;
}

static size_t
rounds_binary(size_t n)
{
    size_t r = 0;
    while (n > 1)
    {
        n >>= 1;
        ++r;
    }
    return r;
}

static size_t
next_power_of_two(size_t n)
{
    if (n <= 1)
        return 1;

    size_t p = 1;
    while (p < n)
    {
        if (p > SIZE_MAX / 2)
            return 0;
        p <<= 1;
    }
    return p;
}

static size_t
rounds_3w(size_t n)
{
    size_t r = 0;
    while (n > 1)
    {
        n = (n + 2) / 3; /* ceil(n/3), i.e. dynamic padding then /3 */
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

/* P = <a,G> + <b,H> + ux*<a,b>*U. Setup only; not timed. */
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

static void
make_transcript_id(unsigned char out[SCALAR_SIZE], size_t n)
{
    static const unsigned char tag[] = "IPA_BENCH";
    memset(out, 0, SCALAR_SIZE);
    memcpy(out, tag, sizeof(tag) - 1);

    uint64_t x = (uint64_t)n;
    for (int i = 0; i < 8; ++i)
    {
        out[SCALAR_SIZE - 1 - i] = (unsigned char)(x & 0xffu);
        x >>= 8;
    }
}

static void
print_stats(
    const char *scheme,
    const char *operation,
    const struct bench_stats *s)
{
    printf(
        "  %-7s %-6s  mean %9.3f ms   median %9.3f ms   "
        "min %9.3f ms   p95 %9.3f ms   max %9.3f ms\n",
        scheme,
        operation,
        s->mean_ms,
        s->median_ms,
        s->min_ms,
        s->p95_ms,
        s->max_ms);
}

static int
benchmark_n(
    secp256k1_context *ctx,
    size_t logical_n,
    size_t prove_iters,
    size_t verify_iters)
{
    const size_t n = logical_n;
    const size_t binary_n = next_power_of_two(n);
    if (binary_n == 0)
        return 0;

    const size_t rb = rounds_binary(binary_n);
    const size_t r3 = rounds_3w(n);
    const size_t re = rounds_3w_et(n);
    const size_t te = terminal_len_3w_et(n);

    secp256k1_pubkey *G = NULL, *H = NULL;
    secp256k1_pubkey *Gb_work = NULL, *Hb_work = NULL;
    unsigned char *a = NULL, *b = NULL;
    unsigned char *ab_work = NULL, *bb_work = NULL;

    secp256k1_pubkey *Lb = NULL, *Rb = NULL;
    secp256k1_pubkey *L1 = NULL, *L2 = NULL, *R1 = NULL, *R2 = NULL;
    secp256k1_pubkey *E_L1 = NULL, *E_L2 = NULL, *E_R1 = NULL, *E_R2 = NULL;

    double *samples = NULL;

    secp256k1_pubkey U, P;
    unsigned char dot[SCALAR_SIZE], ux[SCALAR_SIZE], transcript[SCALAR_SIZE];
    unsigned char af_b[SCALAR_SIZE], bf_b[SCALAR_SIZE];
    unsigned char af_3[SCALAR_SIZE], bf_3[SCALAR_SIZE];
    unsigned char a_et[3 * SCALAR_SIZE], b_et[3 * SCALAR_SIZE];
    size_t rounds_out = 0, terminal_n_out = 0;
    int ok = 0;

    G = (secp256k1_pubkey *)malloc(binary_n * sizeof(*G));
    H = (secp256k1_pubkey *)malloc(binary_n * sizeof(*H));
    Gb_work = (secp256k1_pubkey *)malloc(binary_n * sizeof(*Gb_work));
    Hb_work = (secp256k1_pubkey *)malloc(binary_n * sizeof(*Hb_work));

    a = (unsigned char *)calloc(binary_n, SCALAR_SIZE);
    b = (unsigned char *)calloc(binary_n, SCALAR_SIZE);
    ab_work = (unsigned char *)malloc(binary_n * SCALAR_SIZE);
    bb_work = (unsigned char *)malloc(binary_n * SCALAR_SIZE);

    Lb = (secp256k1_pubkey *)malloc(rb * sizeof(*Lb));
    Rb = (secp256k1_pubkey *)malloc(rb * sizeof(*Rb));

    L1 = (secp256k1_pubkey *)malloc(r3 * sizeof(*L1));
    L2 = (secp256k1_pubkey *)malloc(r3 * sizeof(*L2));
    R1 = (secp256k1_pubkey *)malloc(r3 * sizeof(*R1));
    R2 = (secp256k1_pubkey *)malloc(r3 * sizeof(*R2));

    if (re > 0)
    {
        E_L1 = (secp256k1_pubkey *)malloc(re * sizeof(*E_L1));
        E_L2 = (secp256k1_pubkey *)malloc(re * sizeof(*E_L2));
        E_R1 = (secp256k1_pubkey *)malloc(re * sizeof(*E_R1));
        E_R2 = (secp256k1_pubkey *)malloc(re * sizeof(*E_R2));
    }

    samples = (double *)malloc(
        (prove_iters > verify_iters ? prove_iters : verify_iters) *
        sizeof(*samples));

    if (!G || !H || !Gb_work || !Hb_work || !a || !b ||
        !ab_work || !bb_work || !Lb || !Rb || !L1 || !L2 || !R1 || !R2 ||
        (re > 0 && (!E_L1 || !E_L2 || !E_R1 || !E_R2)) || !samples)
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, G, binary_n, (const unsigned char *)"IPA_B_G", 7))
        goto cleanup;
    if (!secp256k1_mpt_get_generator_vector(
            ctx, H, binary_n, (const unsigned char *)"IPA_B_H", 7))
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

    /* Build one proof for each scheme and sanity-check them. */
    memcpy(Gb_work, G, binary_n * sizeof(*G));
    memcpy(Hb_work, H, binary_n * sizeof(*H));
    memcpy(ab_work, a, binary_n * SCALAR_SIZE);
    memcpy(bb_work, b, binary_n * SCALAR_SIZE);

    if (!secp256k1_bulletproof_run_ipa_prover(
            ctx, &U, Gb_work, Hb_work, ab_work, bb_work, binary_n,
            transcript, ux, Lb, Rb, rb, &rounds_out, af_b, bf_b) ||
        rounds_out != rb)
        goto cleanup;

    if (!secp256k1_bulletproof_run_ipa_prover_3w(
            ctx, &U, G, H, a, b, n, transcript, ux,
            L1, L2, R1, R2, r3, &rounds_out, af_3, bf_3) ||
        rounds_out != r3)
        goto cleanup;

    if (!secp256k1_bulletproof_run_ipa_prover_3w_et(
            ctx, &U, G, H, a, b, n, transcript, ux,
            E_L1, E_L2, E_R1, E_R2, re, &rounds_out,
            a_et, b_et, &terminal_n_out) ||
        rounds_out != re || terminal_n_out != te)
        goto cleanup;

    if (!ipa_verify_explicit(
            ctx, G, H, &U, &P, Lb, Rb, binary_n,
            af_b, bf_b, ux, transcript))
    {
        fprintf(stderr, "Binary sanity verification failed at n=%zu\n", n);
        goto cleanup;
    }

    if (!ipa_verify_explicit_3w(
            ctx, G, H, &U, &P, L1, L2, R1, R2, n,
            af_3, bf_3, ux, transcript))
    {
        fprintf(stderr, "Pure 3W sanity verification failed at n=%zu\n", n);
        goto cleanup;
    }

    if (!ipa_verify_explicit_3w_et(
            ctx, G, H, &U, &P, E_L1, E_L2, E_R1, E_R2, n,
            a_et, b_et, ux, transcript))
    {
        fprintf(stderr, "3W-ET sanity verification failed at n=%zu\n", n);
        goto cleanup;
    }

    const size_t binary_ipa_bytes = 2 * rb * 33 + 2 * SCALAR_SIZE;
    const size_t pure_ipa_bytes = 4 * r3 * 33 + 2 * SCALAR_SIZE;
    const size_t et_ipa_bytes = 4 * re * 33 + 2 * te * SCALAR_SIZE;

    const size_t binary_bp_style = 292 + 66 * rb;
    const size_t pure_bp_style = 292 + 132 * r3;
    /* 4 outer points + t_hat,tau_x,mu + the ET IPA payload. */
    const size_t et_bp_style = 228 + et_ipa_bytes;

    printf("\n============================================================\n");
    printf("IPA benchmark logical n=%zu\n", n);
    printf(
        "  Binary  padded n=%zu, rounds=%zu, IPA bytes=%zu, BP-style=%zu\n",
        binary_n, rb, binary_ipa_bytes, binary_bp_style);
    printf(
        "  Pure3W  direct n=%zu, rounds=%zu, IPA bytes=%zu, BP-style=%zu\n",
        n, r3, pure_ipa_bytes, pure_bp_style);
    printf(
        "  3W-ET   direct n=%zu, rounds=%zu, terminal=%zu, "
        "IPA bytes=%zu, BP-style=%zu\n",
        n, re, te, et_ipa_bytes, et_bp_style);
    printf(
        "  Iterations: prove=%zu, verify=%zu, warmup=%d\n",
        prove_iters, verify_iters, WARMUP_ITERS);

    /* Warm-up all three implementations. */
    for (int w = 0; w < WARMUP_ITERS; ++w)
    {
        memcpy(Gb_work, G, binary_n * sizeof(*G));
        memcpy(Hb_work, H, binary_n * sizeof(*H));
        memcpy(ab_work, a, binary_n * SCALAR_SIZE);
        memcpy(bb_work, b, binary_n * SCALAR_SIZE);

        if (!secp256k1_bulletproof_run_ipa_prover(
                ctx, &U, Gb_work, Hb_work, ab_work, bb_work, binary_n,
                transcript, ux, Lb, Rb, rb, &rounds_out, af_b, bf_b))
            goto cleanup;

        if (!secp256k1_bulletproof_run_ipa_prover_3w(
                ctx, &U, G, H, a, b, n, transcript, ux,
                L1, L2, R1, R2, r3, &rounds_out, af_3, bf_3))
            goto cleanup;

        if (!secp256k1_bulletproof_run_ipa_prover_3w_et(
                ctx, &U, G, H, a, b, n, transcript, ux,
                E_L1, E_L2, E_R1, E_R2, re, &rounds_out,
                a_et, b_et, &terminal_n_out))
            goto cleanup;

        if (!ipa_verify_explicit(
                ctx, G, H, &U, &P, Lb, Rb, binary_n,
                af_b, bf_b, ux, transcript))
            goto cleanup;

        if (!ipa_verify_explicit_3w(
                ctx, G, H, &U, &P, L1, L2, R1, R2, n,
                af_3, bf_3, ux, transcript))
            goto cleanup;

        if (!ipa_verify_explicit_3w_et(
                ctx, G, H, &U, &P, E_L1, E_L2, E_R1, E_R2, n,
                a_et, b_et, ux, transcript))
            goto cleanup;
    }

    /* Binary prover. */
    for (size_t i = 0; i < prove_iters; ++i)
    {
        memcpy(Gb_work, G, binary_n * sizeof(*G));
        memcpy(Hb_work, H, binary_n * sizeof(*H));
        memcpy(ab_work, a, binary_n * SCALAR_SIZE);
        memcpy(bb_work, b, binary_n * SCALAR_SIZE);

        const uint64_t t0 = now_ns();
        int r = secp256k1_bulletproof_run_ipa_prover(
            ctx, &U, Gb_work, Hb_work, ab_work, bb_work, binary_n,
            transcript, ux, Lb, Rb, rb, &rounds_out, af_b, bf_b);
        const uint64_t t1 = now_ns();
        if (!r)
            goto cleanup;
        samples[i] = (double)(t1 - t0) / 1000000.0;
    }
    struct bench_stats binary_prove = summarize(samples, prove_iters);

    /* Pure 3W prover. */
    for (size_t i = 0; i < prove_iters; ++i)
    {
        const uint64_t t0 = now_ns();
        int r = secp256k1_bulletproof_run_ipa_prover_3w(
            ctx, &U, G, H, a, b, n, transcript, ux,
            L1, L2, R1, R2, r3, &rounds_out, af_3, bf_3);
        const uint64_t t1 = now_ns();
        if (!r)
            goto cleanup;
        samples[i] = (double)(t1 - t0) / 1000000.0;
    }
    struct bench_stats pure_prove = summarize(samples, prove_iters);

    /* 3W + early-termination prover. */
    for (size_t i = 0; i < prove_iters; ++i)
    {
        const uint64_t t0 = now_ns();
        int r = secp256k1_bulletproof_run_ipa_prover_3w_et(
            ctx, &U, G, H, a, b, n, transcript, ux,
            E_L1, E_L2, E_R1, E_R2, re, &rounds_out,
            a_et, b_et, &terminal_n_out);
        const uint64_t t1 = now_ns();
        if (!r)
            goto cleanup;
        samples[i] = (double)(t1 - t0) / 1000000.0;
    }
    struct bench_stats et_prove = summarize(samples, prove_iters);

    /* Recreate stable binary proof. */
    memcpy(Gb_work, G, binary_n * sizeof(*G));
    memcpy(Hb_work, H, binary_n * sizeof(*H));
    memcpy(ab_work, a, binary_n * SCALAR_SIZE);
    memcpy(bb_work, b, binary_n * SCALAR_SIZE);
    if (!secp256k1_bulletproof_run_ipa_prover(
            ctx, &U, Gb_work, Hb_work, ab_work, bb_work, binary_n,
            transcript, ux, Lb, Rb, rb, &rounds_out, af_b, bf_b))
        goto cleanup;

    for (size_t i = 0; i < verify_iters; ++i)
    {
        const uint64_t t0 = now_ns();
        int r = ipa_verify_explicit(
            ctx, G, H, &U, &P, Lb, Rb, binary_n,
            af_b, bf_b, ux, transcript);
        const uint64_t t1 = now_ns();
        if (!r)
            goto cleanup;
        samples[i] = (double)(t1 - t0) / 1000000.0;
    }
    struct bench_stats binary_verify = summarize(samples, verify_iters);

    /* Recreate stable pure-3W proof. */
    if (!secp256k1_bulletproof_run_ipa_prover_3w(
            ctx, &U, G, H, a, b, n, transcript, ux,
            L1, L2, R1, R2, r3, &rounds_out, af_3, bf_3))
        goto cleanup;

    for (size_t i = 0; i < verify_iters; ++i)
    {
        const uint64_t t0 = now_ns();
        int r = ipa_verify_explicit_3w(
            ctx, G, H, &U, &P, L1, L2, R1, R2, n,
            af_3, bf_3, ux, transcript);
        const uint64_t t1 = now_ns();
        if (!r)
            goto cleanup;
        samples[i] = (double)(t1 - t0) / 1000000.0;
    }
    struct bench_stats pure_verify = summarize(samples, verify_iters);

    /* Recreate stable ET proof. */
    if (!secp256k1_bulletproof_run_ipa_prover_3w_et(
            ctx, &U, G, H, a, b, n, transcript, ux,
            E_L1, E_L2, E_R1, E_R2, re, &rounds_out,
            a_et, b_et, &terminal_n_out))
        goto cleanup;

    for (size_t i = 0; i < verify_iters; ++i)
    {
        const uint64_t t0 = now_ns();
        int r = ipa_verify_explicit_3w_et(
            ctx, G, H, &U, &P, E_L1, E_L2, E_R1, E_R2, n,
            a_et, b_et, ux, transcript);
        const uint64_t t1 = now_ns();
        if (!r)
            goto cleanup;
        samples[i] = (double)(t1 - t0) / 1000000.0;
    }
    struct bench_stats et_verify = summarize(samples, verify_iters);

    print_stats("Binary", "prove", &binary_prove);
    print_stats("Pure3W", "prove", &pure_prove);
    print_stats("3W-ET", "prove", &et_prove);
    print_stats("Binary", "verify", &binary_verify);
    print_stats("Pure3W", "verify", &pure_verify);
    print_stats("3W-ET", "verify", &et_verify);

    printf(
        "\n  Median speedups Binary / 3W-ET: prove %.3fx, verify %.3fx\n",
        binary_prove.median_ms / et_prove.median_ms,
        binary_verify.median_ms / et_verify.median_ms);

    printf(
        "  ET speedups Pure3W / 3W-ET:   prove %.3fx, verify %.3fx\n",
        pure_prove.median_ms / et_prove.median_ms,
        pure_verify.median_ms / et_verify.median_ms);

    printf(
        "  ET median change vs Pure3W:   prove %+7.2f%%, verify %+7.2f%%\n",
        100.0 * (et_prove.median_ms / pure_prove.median_ms - 1.0),
        100.0 * (et_verify.median_ms / pure_verify.median_ms - 1.0));

    printf(
        "  ET IPA-size change vs Pure3W: %+zd bytes (%+.2f%%)\n",
        (ptrdiff_t)et_ipa_bytes - (ptrdiff_t)pure_ipa_bytes,
        100.0 * ((double)et_ipa_bytes / (double)pure_ipa_bytes - 1.0));

    ok = 1;

cleanup:
    free(G);
    free(H);
    free(Gb_work);
    free(Hb_work);
    free(a);
    free(b);
    free(ab_work);
    free(bb_work);
    free(Lb);
    free(Rb);
    free(L1);
    free(L2);
    free(R1);
    free(R2);
    free(E_L1);
    free(E_L2);
    free(E_R1);
    free(E_R2);
    free(samples);
    return ok;
}

static size_t
parse_iterations(const char *s, size_t fallback)
{
    if (!s)
        return fallback;

    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 10);
    if (!end || *end != '\0' || v == 0)
        return fallback;

    return (size_t)v;
}

int
main(int argc, char **argv)
{
    const size_t prove_iters =
        parse_iterations(argc > 1 ? argv[1] : NULL, 50);
    const size_t verify_iters =
        parse_iterations(argc > 2 ? argv[2] : NULL, 200);

    secp256k1_context *ctx =
        secp256k1_context_create(
            SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    if (!ctx)
    {
        fprintf(stderr, "Could not create secp256k1 context\n");
        return 1;
    }

    /*
     * Mix binary-friendly powers of two, 3W-friendly lengths, and awkward
     * general lengths.  Binary is zero-padded to the next power of two;
     * 3W uses the logical length directly with dynamic per-round padding.
     */
    static const size_t sizes[] = {
        /* Around 64 */
        55, 56, 57, 58, 59,
        60, 61, 62, 63, 64,
        65, 66, 67, 68, 69,
        70, 71, 72, 73, 74, 75,

        /* Around 128 */
        115, 116, 117, 118, 119,
        120, 121, 122, 123, 124,
        125, 126, 127, 128,
        129, 130, 131, 132, 133,
        134, 135, 136, 137, 138,
        139, 140,

        /* Around 200 / 243 / 256 */
        190, 195, 200, 205, 210,
        220, 230, 240, 241, 242,
        243, 244, 245, 250, 255,
        256, 257, 260
    };

    printf("Binary vs Pure 3W vs 3W+Early-Termination IPA microbenchmark\n");
    printf("Arbitrary logical lengths enabled:\n");
    printf("  Binary -> zero-pad to next power of two\n");
    printf("  3W     -> use logical n with dynamic per-round padding\n");
    printf("Timing source: CLOCK_MONOTONIC_RAW when available\n");
    printf("Build should be Release (-O3 / NDEBUG) for meaningful results.\n");

    for (size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i)
    {
        if (!benchmark_n(ctx, sizes[i], prove_iters, verify_iters))
        {
            fprintf(stderr, "\nBenchmark failed for n=%zu\n", sizes[i]);
            secp256k1_context_destroy(ctx);
            return 1;
        }
    }

    secp256k1_context_destroy(ctx);
    printf("\nBenchmark completed successfully.\n");
    return 0;
}
