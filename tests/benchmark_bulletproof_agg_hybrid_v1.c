#include "secp256k1_mpt.h"
#include "test_utils.h"
#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define BP_VALUE_BITS 64
#define BP_TOTAL_BITS(m) ((size_t)(BP_VALUE_BITS * (m)))

extern int secp256k1_bulletproof_ipa_hybrid_v1_schedule(
    size_t n, size_t k3,
    size_t *r3_out, size_t *r2_out, size_t *terminal_n_out);

extern int secp256k1_bulletproof_prove_agg_hybrid_v1(
    const secp256k1_context *ctx,
    unsigned char *proof_out,
    size_t *proof_len,
    const uint64_t *values,
    const unsigned char *blindings_flat,
    size_t m,
    size_t k3,
    const secp256k1_pubkey *h_generator,
    const unsigned char *context_id);

extern int secp256k1_bulletproof_verify_agg_hybrid_v1(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const unsigned char *proof,
    size_t proof_len,
    const secp256k1_pubkey *commitment_C_vec,
    size_t m,
    size_t k3,
    const secp256k1_pubkey *h_generator,
    const unsigned char *context_id);

typedef struct
{
  double mean;
  double median;
  double min;
  double p95;
  double max;
} stats_t;

static void bench_now(struct timespec *ts)
{
#if defined(CLOCK_MONOTONIC_RAW)
  clock_gettime(CLOCK_MONOTONIC_RAW, ts);
#elif defined(CLOCK_MONOTONIC)
  clock_gettime(CLOCK_MONOTONIC, ts);
#else
  timespec_get(ts, TIME_UTC);
#endif
}

static double elapsed_ms(const struct timespec *a, const struct timespec *b)
{
  return (double)(b->tv_sec - a->tv_sec) * 1000.0 +
         (double)(b->tv_nsec - a->tv_nsec) / 1.0e6;
}

static int cmp_double(const void *a, const void *b)
{
  const double da = *(const double *)a;
  const double db = *(const double *)b;
  return (da > db) - (da < db);
}

static stats_t compute_stats(const double *samples, size_t n)
{
  stats_t s = {0};
  double *tmp = NULL;
  double sum = 0.0;

  if (!samples || n == 0)
    return s;

  tmp = (double *)malloc(n * sizeof(*tmp));
  if (!tmp)
  {
    fprintf(stderr, "allocation failure in compute_stats\n");
    exit(2);
  }

  memcpy(tmp, samples, n * sizeof(*tmp));
  qsort(tmp, n, sizeof(*tmp), cmp_double);

  for (size_t i = 0; i < n; ++i)
    sum += samples[i];

  s.mean = sum / (double)n;
  s.min = tmp[0];
  s.max = tmp[n - 1];

  if (n & 1u)
    s.median = tmp[n / 2];
  else
    s.median = 0.5 * (tmp[n / 2 - 1] + tmp[n / 2]);

  /* Nearest-rank p95: ceil(0.95*n), clamped to [1,n]. */
  {
    size_t rank = (95 * n + 99) / 100;
    if (rank < 1)
      rank = 1;
    if (rank > n)
      rank = n;
    s.p95 = tmp[rank - 1];
  }

  free(tmp);
  return s;
}

static void print_stats(const char *label, const stats_t *s)
{
  printf("    %-8s mean %8.3f  median %8.3f  min %8.3f  p95 %8.3f  max %8.3f ms\n",
         label, s->mean, s->median, s->min, s->p95, s->max);
}

static size_t max_k3_for_n(size_t n)
{
  size_t r = 0;
  while (n > 3)
  {
    n = (n + 2) / 3;
    ++r;
  }
  return r;
}

static void make_context_id(unsigned char out[32], size_t m)
{
  memset(out, 0, 32);
  memcpy(out, "HYBRID_V1_FULL_BP_BENCH", 23);
  out[31] = (unsigned char)m;
}

static int setup_case(
    secp256k1_context *ctx,
    const uint64_t *values,
    size_t m,
    unsigned char (**blindings_out)[32],
    secp256k1_pubkey **commitments_out,
    secp256k1_pubkey **G_vec_out,
    secp256k1_pubkey **H_vec_out,
    secp256k1_pubkey *h_generator,
    unsigned char context_id[32])
{
  const size_t n = BP_TOTAL_BITS(m);
  unsigned char (*blindings)[32] = NULL;
  secp256k1_pubkey *commitments = NULL;
  secp256k1_pubkey *G_vec = NULL;
  secp256k1_pubkey *H_vec = NULL;

  blindings = malloc(m * sizeof(*blindings));
  commitments = malloc(m * sizeof(*commitments));
  G_vec = malloc(n * sizeof(*G_vec));
  H_vec = malloc(n * sizeof(*H_vec));

  if (!blindings || !commitments || !G_vec || !H_vec)
    goto fail;

  make_context_id(context_id, m);

  if (!secp256k1_mpt_get_h_generator(ctx, h_generator))
    goto fail;

  if (!secp256k1_mpt_get_generator_vector(
          ctx, G_vec, n, (const unsigned char *)"BP_G", 4))
    goto fail;

  if (!secp256k1_mpt_get_generator_vector(
          ctx, H_vec, n, (const unsigned char *)"BP_H", 4))
    goto fail;

  for (size_t i = 0; i < m; ++i)
  {
    random_scalar(ctx, blindings[i]);
    if (!secp256k1_bulletproof_create_commitment(
            ctx, &commitments[i], values[i], blindings[i], h_generator))
      goto fail;
  }

  *blindings_out = blindings;
  *commitments_out = commitments;
  *G_vec_out = G_vec;
  *H_vec_out = H_vec;
  return 1;

fail:
  free(blindings);
  free(commitments);
  free(G_vec);
  free(H_vec);
  return 0;
}

static int bench_standard_3w(
    secp256k1_context *ctx,
    const uint64_t *values,
    const unsigned char *blindings_flat,
    size_t m,
    const secp256k1_pubkey *commitments,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *h_generator,
    const unsigned char context_id[32],
    size_t prove_iters,
    size_t verify_iters,
    size_t warmups)
{
  size_t proof_len = 0;
  unsigned char *proof = NULL;
  double *prove_samples = NULL;
  double *verify_samples = NULL;
  int ok = 0;

  if (!secp256k1_bulletproof_prove_agg(
          ctx, NULL, &proof_len, values, blindings_flat, m,
          h_generator, context_id))
    goto cleanup;

  proof = malloc(proof_len);
  prove_samples = malloc(prove_iters * sizeof(*prove_samples));
  verify_samples = malloc(verify_iters * sizeof(*verify_samples));
  if (!proof || !prove_samples || !verify_samples)
    goto cleanup;

  /* Produce an initial valid proof for verifier warmups. */
  {
    size_t out_len = proof_len;
    if (!secp256k1_bulletproof_prove_agg(
            ctx, proof, &out_len, values, blindings_flat, m,
            h_generator, context_id) ||
        out_len != proof_len)
      goto cleanup;
  }

  if (!secp256k1_bulletproof_verify_agg(
          ctx, G_vec, H_vec, proof, proof_len, commitments, m,
          h_generator, context_id))
    goto cleanup;

  for (size_t i = 0; i < warmups; ++i)
  {
    size_t out_len = proof_len;
    if (!secp256k1_bulletproof_prove_agg(
            ctx, proof, &out_len, values, blindings_flat, m,
            h_generator, context_id))
      goto cleanup;
  }

  for (size_t i = 0; i < prove_iters; ++i)
  {
    struct timespec a, b;
    size_t out_len = proof_len;

    bench_now(&a);
    if (!secp256k1_bulletproof_prove_agg(
            ctx, proof, &out_len, values, blindings_flat, m,
            h_generator, context_id))
      goto cleanup;
    bench_now(&b);

    if (out_len != proof_len)
      goto cleanup;
    prove_samples[i] = elapsed_ms(&a, &b);
  }

  /* Use the last generated proof for verifier measurements. */
  if (!secp256k1_bulletproof_verify_agg(
          ctx, G_vec, H_vec, proof, proof_len, commitments, m,
          h_generator, context_id))
    goto cleanup;

  for (size_t i = 0; i < warmups; ++i)
  {
    if (!secp256k1_bulletproof_verify_agg(
            ctx, G_vec, H_vec, proof, proof_len, commitments, m,
            h_generator, context_id))
      goto cleanup;
  }

  for (size_t i = 0; i < verify_iters; ++i)
  {
    struct timespec a, b;

    bench_now(&a);
    if (!secp256k1_bulletproof_verify_agg(
            ctx, G_vec, H_vec, proof, proof_len, commitments, m,
            h_generator, context_id))
      goto cleanup;
    bench_now(&b);

    verify_samples[i] = elapsed_ms(&a, &b);
  }

  {
    const stats_t ps = compute_stats(prove_samples, prove_iters);
    const stats_t vs = compute_stats(verify_samples, verify_iters);
    printf("  Pure3W  bytes=%zu\n", proof_len);
    print_stats("prove", &ps);
    print_stats("verify", &vs);
  }

  ok = 1;

cleanup:
  free(proof);
  free(prove_samples);
  free(verify_samples);
  return ok;
}

static int bench_hybrid_schedule(
    secp256k1_context *ctx,
    const uint64_t *values,
    const unsigned char *blindings_flat,
    size_t m,
    size_t k3,
    const secp256k1_pubkey *commitments,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *h_generator,
    const unsigned char context_id[32],
    size_t prove_iters,
    size_t verify_iters,
    size_t warmups)
{
  const size_t n = BP_TOTAL_BITS(m);
  size_t r3 = 0, r2 = 0, terminal_n = 0;
  size_t proof_len = 0;
  unsigned char *proof = NULL;
  double *prove_samples = NULL;
  double *verify_samples = NULL;
  int ok = 0;

  if (!secp256k1_bulletproof_ipa_hybrid_v1_schedule(
          n, k3, &r3, &r2, &terminal_n))
    goto cleanup;

  if (!secp256k1_bulletproof_prove_agg_hybrid_v1(
          ctx, NULL, &proof_len, values, blindings_flat, m, k3,
          h_generator, context_id))
    goto cleanup;

  proof = malloc(proof_len);
  prove_samples = malloc(prove_iters * sizeof(*prove_samples));
  verify_samples = malloc(verify_iters * sizeof(*verify_samples));
  if (!proof || !prove_samples || !verify_samples)
    goto cleanup;

  /* Initial proof and correctness check. */
  {
    size_t out_len = proof_len;
    if (!secp256k1_bulletproof_prove_agg_hybrid_v1(
            ctx, proof, &out_len, values, blindings_flat, m, k3,
            h_generator, context_id) ||
        out_len != proof_len)
      goto cleanup;
  }

  if (!secp256k1_bulletproof_verify_agg_hybrid_v1(
          ctx, G_vec, H_vec, proof, proof_len,
          commitments, m, k3, h_generator, context_id))
    goto cleanup;

  for (size_t i = 0; i < warmups; ++i)
  {
    size_t out_len = proof_len;
    if (!secp256k1_bulletproof_prove_agg_hybrid_v1(
            ctx, proof, &out_len, values, blindings_flat, m, k3,
            h_generator, context_id))
      goto cleanup;
  }

  for (size_t i = 0; i < prove_iters; ++i)
  {
    struct timespec a, b;
    size_t out_len = proof_len;

    bench_now(&a);
    if (!secp256k1_bulletproof_prove_agg_hybrid_v1(
            ctx, proof, &out_len, values, blindings_flat, m, k3,
            h_generator, context_id))
      goto cleanup;
    bench_now(&b);

    if (out_len != proof_len)
      goto cleanup;
    prove_samples[i] = elapsed_ms(&a, &b);
  }

  if (!secp256k1_bulletproof_verify_agg_hybrid_v1(
          ctx, G_vec, H_vec, proof, proof_len,
          commitments, m, k3, h_generator, context_id))
    goto cleanup;

  for (size_t i = 0; i < warmups; ++i)
  {
    if (!secp256k1_bulletproof_verify_agg_hybrid_v1(
            ctx, G_vec, H_vec, proof, proof_len,
            commitments, m, k3, h_generator, context_id))
      goto cleanup;
  }

  for (size_t i = 0; i < verify_iters; ++i)
  {
    struct timespec a, b;

    bench_now(&a);
    if (!secp256k1_bulletproof_verify_agg_hybrid_v1(
            ctx, G_vec, H_vec, proof, proof_len,
            commitments, m, k3, h_generator, context_id))
      goto cleanup;
    bench_now(&b);

    verify_samples[i] = elapsed_ms(&a, &b);
  }

  {
    const stats_t ps = compute_stats(prove_samples, prove_iters);
    const stats_t vs = compute_stats(verify_samples, verify_iters);

    printf("  H%-2zu     r3=%zu r2=%zu t=%zu bytes=%zu\n",
           k3, r3, r2, terminal_n, proof_len);
    print_stats("prove", &ps);
    print_stats("verify", &vs);
  }

  ok = 1;

cleanup:
  free(proof);
  free(prove_samples);
  free(verify_samples);
  return ok;
}

static int run_case(
    secp256k1_context *ctx,
    const char *name,
    const uint64_t *values,
    size_t m,
    size_t prove_iters,
    size_t verify_iters,
    size_t warmups)
{
  const size_t n = BP_TOTAL_BITS(m);
  const size_t max_k3 = max_k3_for_n(n);

  unsigned char (*blindings)[32] = NULL;
  secp256k1_pubkey *commitments = NULL;
  secp256k1_pubkey *G_vec = NULL;
  secp256k1_pubkey *H_vec = NULL;
  secp256k1_pubkey h_generator;
  unsigned char context_id[32];
  int ok = 0;

  if (!setup_case(
          ctx, values, m, &blindings, &commitments,
          &G_vec, &H_vec, &h_generator, context_id))
    goto cleanup;

  printf("\n[FULL-BP-BENCH] %s  m=%zu n=%zu\n", name, m, n);

  if (!bench_standard_3w(
          ctx, values, (const unsigned char *)blindings, m,
          commitments, G_vec, H_vec, &h_generator, context_id,
          prove_iters, verify_iters, warmups))
    goto cleanup;

  for (size_t k3 = 0; k3 <= max_k3; ++k3)
  {
    if (!bench_hybrid_schedule(
            ctx, values, (const unsigned char *)blindings, m, k3,
            commitments, G_vec, H_vec, &h_generator, context_id,
            prove_iters, verify_iters, warmups))
      goto cleanup;
  }

  ok = 1;

cleanup:
  free(blindings);
  free(commitments);
  free(G_vec);
  free(H_vec);
  return ok;
}

int main(int argc, char **argv)
{
  size_t prove_iters = 20;
  size_t verify_iters = 100;
  size_t warmups = 10;

  if (argc > 1)
    prove_iters = (size_t)strtoull(argv[1], NULL, 10);
  if (argc > 2)
    verify_iters = (size_t)strtoull(argv[2], NULL, 10);
  if (argc > 3)
    warmups = (size_t)strtoull(argv[3], NULL, 10);

  if (prove_iters == 0 || verify_iters == 0)
  {
    fprintf(stderr,
            "usage: %s [prove_iters=20] [verify_iters=100] [warmups=10]\n",
            argv[0]);
    return 2;
  }

  printf("Full aggregated Bulletproof Hybrid-v1 benchmark\n");
  printf("  prove_iters=%zu verify_iters=%zu warmups=%zu\n",
         prove_iters, verify_iters, warmups);
  printf("  verifier: Hybrid-v1 fast verifier\n");
  printf("  statistics: mean median min p95 max\n");

  secp256k1_context *ctx = secp256k1_context_create(
      SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
  if (!ctx)
  {
    fprintf(stderr, "failed to create secp256k1 context\n");
    return 1;
  }

  {
    const uint64_t values[] = {UINT64_C(0x123456789abcdef0)};
    if (!run_case(ctx, "single-value", values, 1,
                  prove_iters, verify_iters, warmups))
      goto fail;
  }

  {
    const uint64_t values[] = {
        UINT64_C(0x0123456789abcdef),
        UINT64_C(0xfedcba9876543210)};
    if (!run_case(ctx, "two-value aggregate", values, 2,
                  prove_iters, verify_iters, warmups))
      goto fail;
  }

  {
    const uint64_t values[] = {
        UINT64_C(0x0123456789abcdef),
        UINT64_C(0x1111222233334444),
        UINT64_C(0x5555666677778888),
        UINT64_C(0xfedcba9876543210)};
    if (!run_case(ctx, "four-value aggregate", values, 4,
                  prove_iters, verify_iters, warmups))
      goto fail;
  }

  secp256k1_context_destroy(ctx);
  printf("\n[SUCCESS] Full aggregated Bulletproof benchmark completed.\n");
  return 0;

fail:
  secp256k1_context_destroy(ctx);
  fprintf(stderr, "\n[FAIL] Full aggregated Bulletproof benchmark failed.\n");
  return 1;
}
