#include "secp256k1_mpt.h"
#include "test_utils.h"

#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

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

extern int ipa_verify_hybrid_v1_fast(
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

struct stats {
    double mean;
    double median;
    double min;
    double p95;
    double max;
};

static int cmp_double(const void *a, const void *b)
{
    const double x = *(const double *)a;
    const double y = *(const double *)b;
    return (x > y) - (x < y);
}

static struct stats summarize(double *v, size_t n)
{
    struct stats s = {0};
    double sum = 0.0;

    qsort(v, n, sizeof(*v), cmp_double);

    for (size_t i = 0; i < n; ++i)
        sum += v[i];

    s.mean = sum / (double)n;
    s.min = v[0];
    s.max = v[n - 1];

    if (n & 1u)
        s.median = v[n / 2];
    else
        s.median = 0.5 * (v[n / 2 - 1] + v[n / 2]);

    {
        size_t p95_index = (size_t)(0.95 * (double)(n - 1));
        s.p95 = v[p95_index];
    }

    return s;
}

static uint64_t now_ns(void)
{
#if defined(CLOCK_MONOTONIC_RAW)
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
#endif
}

static int scalar_zero(const unsigned char s[SCALAR_SIZE])
{
    unsigned char z[SCALAR_SIZE] = {0};
    return memcmp(s, z, SCALAR_SIZE) == 0;
}

static int add_term(
    const secp256k1_context *ctx,
    secp256k1_pubkey *acc,
    int *inited,
    const secp256k1_pubkey *term)
{
    if (!*inited) {
        *acc = *term;
        *inited = 1;
        return 1;
    }

    {
        secp256k1_pubkey sum;
        const secp256k1_pubkey *pts[2] = {acc, term};
        if (!secp256k1_ec_pubkey_combine(ctx, &sum, pts, 2))
            return 0;
        *acc = sum;
    }

    return 1;
}

static int build_P(
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

    for (size_t i = 0; i < n; ++i) {
        const unsigned char *ai = a + i * SCALAR_SIZE;
        const unsigned char *bi = b + i * SCALAR_SIZE;

        if (!scalar_zero(ai)) {
            tmp = G[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, ai) ||
                !add_term(ctx, P, &inited, &tmp))
                return 0;
        }

        if (!scalar_zero(bi)) {
            tmp = H[i];
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, bi) ||
                !add_term(ctx, P, &inited, &tmp))
                return 0;
        }
    }

    {
        unsigned char s[SCALAR_SIZE];
        secp256k1_mpt_scalar_mul(s, dot, ux);

        if (!scalar_zero(s)) {
            tmp = *U;
            if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, s) ||
                !add_term(ctx, P, &inited, &tmp))
                return 0;
        }
    }

    return inited;
}

static void make_transcript(unsigned char out[SCALAR_SIZE], size_t n)
{
    static const unsigned char tag[] = "HYB1_BENCH";
    uint64_t x = (uint64_t)n;

    memset(out, 0, SCALAR_SIZE);
    memcpy(out, tag, sizeof(tag) - 1);

    for (int i = 0; i < 8; ++i) {
        out[SCALAR_SIZE - 1 - i] = (unsigned char)(x & 0xffu);
        x >>= 8;
    }
}

static size_t max_k3(size_t n)
{
    size_t r = 0;
    while (n > 3) {
        n = (n + 2) / 3;
        ++r;
    }
    return r;
}

static void print_stats(const char *label, const struct stats *s)
{
    printf(
        "    %-10s mean %8.3f  median %8.3f  min %8.3f  p95 %8.3f  max %8.3f ms\n",
        label, s->mean, s->median, s->min, s->p95, s->max);
}

static int run_n(
    secp256k1_context *ctx,
    size_t n,
    size_t prove_iters,
    size_t verify_iters,
    size_t warmup)
{
    secp256k1_pubkey *G = NULL, *H = NULL;
    unsigned char *a = NULL, *b = NULL;
    double *samples = NULL;

    secp256k1_pubkey U, P;
    unsigned char dot[SCALAR_SIZE] = {0};
    unsigned char ux[SCALAR_SIZE] = {0};
    unsigned char transcript[SCALAR_SIZE] = {0};

    const size_t mk3 = max_k3(n);
    int ok = 0;

    G = malloc(n * sizeof(*G));
    H = malloc(n * sizeof(*H));
    a = malloc(n * SCALAR_SIZE);
    b = malloc(n * SCALAR_SIZE);
    samples = malloc(
        (prove_iters > verify_iters ? prove_iters : verify_iters) *
        sizeof(*samples));

    if (!G || !H || !a || !b || !samples)
        goto cleanup;

    if (!secp256k1_mpt_get_generator_vector(
            ctx, G, n, (const unsigned char *)"HYB1_BENCH_G", 12) ||
        !secp256k1_mpt_get_generator_vector(
            ctx, H, n, (const unsigned char *)"HYB1_BENCH_H", 12) ||
        !secp256k1_mpt_get_generator_vector(
            ctx, &U, 1, (const unsigned char *)"HYB1_BENCH_U", 12))
        goto cleanup;

    for (size_t i = 0; i < n; ++i) {
        random_scalar(ctx, a + i * SCALAR_SIZE);
        random_scalar(ctx, b + i * SCALAR_SIZE);
    }

    if (!secp256k1_bulletproof_ipa_dot(ctx, dot, a, b, n))
        goto cleanup;

    make_transcript(transcript, n);

    if (!derive_ipa_binding_challenge(ctx, ux, transcript, dot) ||
        !build_P(ctx, &P, G, H, &U, a, b, n, ux, dot))
        goto cleanup;

    printf("\n============================================================\n");
    printf("Hybrid-v1 benchmark logical n=%zu\n", n);
    printf("  Hk = k initial 3W rounds, then dynamic 2W, ET at t<=3\n");
    printf("  Iterations: prove=%zu verify=%zu warmup=%zu\n",
           prove_iters, verify_iters, warmup);
    printf("\n");
    printf("  sched   r3   r2   t   bytes    prove-med   explicit-med   fast-med   fast/expl\n");
    printf("  -----  ---  ---  --  -----    ---------   ------------   --------   ---------\n");

    for (size_t k3 = 0; k3 <= mk3; ++k3) {
        size_t r3 = 0, r2 = 0, t = 0;
        size_t pr3 = 0, pr2 = 0, pt = 0;
        size_t bytes = 0;

        secp256k1_pubkey *L1 = NULL, *L2 = NULL, *R1 = NULL, *R2 = NULL;
        secp256k1_pubkey *Lb = NULL, *Rb = NULL;
        unsigned char at[TERMINAL_MAX * SCALAR_SIZE] = {0};
        unsigned char bt[TERMINAL_MAX * SCALAR_SIZE] = {0};

        struct stats prove_s, explicit_s, fast_s;

        if (!secp256k1_bulletproof_ipa_hybrid_v1_schedule(
                n, k3, &r3, &r2, &t))
            goto cleanup;

        bytes = 132 * r3 + 66 * r2 + 64 * t;

        L1 = calloc(r3 ? r3 : 1, sizeof(*L1));
        L2 = calloc(r3 ? r3 : 1, sizeof(*L2));
        R1 = calloc(r3 ? r3 : 1, sizeof(*R1));
        R2 = calloc(r3 ? r3 : 1, sizeof(*R2));
        Lb = calloc(r2 ? r2 : 1, sizeof(*Lb));
        Rb = calloc(r2 ? r2 : 1, sizeof(*Rb));

        if (!L1 || !L2 || !R1 || !R2 || !Lb || !Rb)
            goto schedule_cleanup;

        if (!secp256k1_bulletproof_run_ipa_prover_hybrid_v1(
                ctx, &U, G, H, a, b, n, k3, transcript, ux,
                r3 ? L1 : NULL, r3 ? L2 : NULL,
                r3 ? R1 : NULL, r3 ? R2 : NULL,
                r3, &pr3,
                r2 ? Lb : NULL, r2 ? Rb : NULL,
                r2, &pr2,
                at, bt, &pt))
            goto schedule_cleanup;

        if (pr3 != r3 || pr2 != r2 || pt != t)
            goto schedule_cleanup;

        if (!ipa_verify_explicit_hybrid_v1(
                ctx, G, H, &U, &P, n, k3,
                r3 ? L1 : NULL, r3 ? L2 : NULL,
                r3 ? R1 : NULL, r3 ? R2 : NULL,
                r2 ? Lb : NULL, r2 ? Rb : NULL,
                at, bt, ux, transcript) ||
            !ipa_verify_hybrid_v1_fast(
                ctx, G, H, &U, &P, n, k3,
                r3 ? L1 : NULL, r3 ? L2 : NULL,
                r3 ? R1 : NULL, r3 ? R2 : NULL,
                r2 ? Lb : NULL, r2 ? Rb : NULL,
                at, bt, ux, transcript))
            goto schedule_cleanup;

        for (size_t w = 0; w < warmup; ++w) {
            size_t wr3 = 0, wr2 = 0, wt = 0;

            if (!secp256k1_bulletproof_run_ipa_prover_hybrid_v1(
                    ctx, &U, G, H, a, b, n, k3, transcript, ux,
                    r3 ? L1 : NULL, r3 ? L2 : NULL,
                    r3 ? R1 : NULL, r3 ? R2 : NULL,
                    r3, &wr3,
                    r2 ? Lb : NULL, r2 ? Rb : NULL,
                    r2, &wr2,
                    at, bt, &wt))
                goto schedule_cleanup;

            if (!ipa_verify_explicit_hybrid_v1(
                    ctx, G, H, &U, &P, n, k3,
                    r3 ? L1 : NULL, r3 ? L2 : NULL,
                    r3 ? R1 : NULL, r3 ? R2 : NULL,
                    r2 ? Lb : NULL, r2 ? Rb : NULL,
                    at, bt, ux, transcript))
                goto schedule_cleanup;

            if (!ipa_verify_hybrid_v1_fast(
                    ctx, G, H, &U, &P, n, k3,
                    r3 ? L1 : NULL, r3 ? L2 : NULL,
                    r3 ? R1 : NULL, r3 ? R2 : NULL,
                    r2 ? Lb : NULL, r2 ? Rb : NULL,
                    at, bt, ux, transcript))
                goto schedule_cleanup;
        }

        for (size_t i = 0; i < prove_iters; ++i) {
            size_t rr3 = 0, rr2 = 0, rt = 0;
            uint64_t t0 = now_ns();

            int r = secp256k1_bulletproof_run_ipa_prover_hybrid_v1(
                ctx, &U, G, H, a, b, n, k3, transcript, ux,
                r3 ? L1 : NULL, r3 ? L2 : NULL,
                r3 ? R1 : NULL, r3 ? R2 : NULL,
                r3, &rr3,
                r2 ? Lb : NULL, r2 ? Rb : NULL,
                r2, &rr2,
                at, bt, &rt);

            uint64_t t1 = now_ns();

            if (!r || rr3 != r3 || rr2 != r2 || rt != t)
                goto schedule_cleanup;

            samples[i] = (double)(t1 - t0) / 1000000.0;
        }
        prove_s = summarize(samples, prove_iters);

        for (size_t i = 0; i < verify_iters; ++i) {
            uint64_t t0 = now_ns();

            int r = ipa_verify_explicit_hybrid_v1(
                ctx, G, H, &U, &P, n, k3,
                r3 ? L1 : NULL, r3 ? L2 : NULL,
                r3 ? R1 : NULL, r3 ? R2 : NULL,
                r2 ? Lb : NULL, r2 ? Rb : NULL,
                at, bt, ux, transcript);

            uint64_t t1 = now_ns();

            if (!r)
                goto schedule_cleanup;

            samples[i] = (double)(t1 - t0) / 1000000.0;
        }
        explicit_s = summarize(samples, verify_iters);

        for (size_t i = 0; i < verify_iters; ++i) {
            uint64_t t0 = now_ns();

            int r = ipa_verify_hybrid_v1_fast(
                ctx, G, H, &U, &P, n, k3,
                r3 ? L1 : NULL, r3 ? L2 : NULL,
                r3 ? R1 : NULL, r3 ? R2 : NULL,
                r2 ? Lb : NULL, r2 ? Rb : NULL,
                at, bt, ux, transcript);

            uint64_t t1 = now_ns();

            if (!r)
                goto schedule_cleanup;

            samples[i] = (double)(t1 - t0) / 1000000.0;
        }
        fast_s = summarize(samples, verify_iters);

        printf(
            "  H%-4zu  %3zu  %3zu  %2zu  %5zu      %8.3f       %8.3f     %8.3f     %7.3fx\n",
            k3, r3, r2, t, bytes,
            prove_s.median, explicit_s.median, fast_s.median,
            explicit_s.median / fast_s.median);

        if (k3 == 0 || k3 == mk3) {
            char label[32];
            snprintf(label, sizeof(label), "H%zu prove", k3);
            print_stats(label, &prove_s);
            snprintf(label, sizeof(label), "H%zu expl", k3);
            print_stats(label, &explicit_s);
            snprintf(label, sizeof(label), "H%zu fast", k3);
            print_stats(label, &fast_s);
        }

        free(L1);
        free(L2);
        free(R1);
        free(R2);
        free(Lb);
        free(Rb);
        continue;

schedule_cleanup:
        free(L1);
        free(L2);
        free(R1);
        free(R2);
        free(Lb);
        free(Rb);
        goto cleanup;
    }

    ok = 1;

cleanup:
    free(G);
    free(H);
    free(a);
    free(b);
    free(samples);
    return ok;
}

int main(int argc, char **argv)
{
    size_t prove_iters = 20;
    size_t verify_iters = 100;
    size_t warmup = 10;

    if (argc >= 2)
        prove_iters = (size_t)strtoull(argv[1], NULL, 10);
    if (argc >= 3)
        verify_iters = (size_t)strtoull(argv[2], NULL, 10);
    if (argc >= 4)
        warmup = (size_t)strtoull(argv[3], NULL, 10);

    if (prove_iters == 0 || verify_iters == 0) {
        fprintf(stderr, "Iterations must be nonzero.\n");
        return 1;
    }

    secp256k1_context *ctx =
        secp256k1_context_create(
            SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);

    if (!ctx) {
        fprintf(stderr, "Could not create secp256k1 context.\n");
        return 1;
    }

    static const size_t dims[] = {
        64, 65, 128, 129, 243, 244, 256, 257
    };

    printf("Hybrid v1 schedule / Pareto benchmark\n");
    printf("Reference verifier = explicit 3W + explicit 2W\n");
    printf("Fast verifier      = explicit 3W + coefficient/MSM 2W suffix\n");
#if defined(CLOCK_MONOTONIC_RAW)
    printf("Timing source: CLOCK_MONOTONIC_RAW\n");
#else
    printf("Timing source: CLOCK_MONOTONIC\n");
#endif
    printf("Use a Release build (-O3 / NDEBUG) for meaningful results.\n");

    for (size_t i = 0; i < sizeof(dims) / sizeof(dims[0]); ++i) {
        if (!run_n(
                ctx, dims[i],
                prove_iters, verify_iters, warmup)) {
            fprintf(stderr, "Benchmark failed at n=%zu\n", dims[i]);
            secp256k1_context_destroy(ctx);
            return 1;
        }
    }

    secp256k1_context_destroy(ctx);
    return 0;
}
