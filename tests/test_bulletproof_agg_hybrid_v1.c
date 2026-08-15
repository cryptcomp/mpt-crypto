#include "secp256k1_mpt.h"
#include "test_utils.h"
#include <secp256k1.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
  memcpy(out, "HYBRID_V1_FULL_BP_TEST", 22);
  out[31] = (unsigned char)m;
}

static void run_full_hybrid_case(
    secp256k1_context *ctx,
    const char *name,
    const uint64_t *values,
    size_t m)
{
  const size_t n = BP_TOTAL_BITS(m);
  const size_t max_k3 = max_k3_for_n(n);

  unsigned char (*blindings)[32] = NULL;
  secp256k1_pubkey *commitments = NULL;
  secp256k1_pubkey *G_vec = NULL;
  secp256k1_pubkey *H_vec = NULL;
  unsigned char context_id[32];
  secp256k1_pubkey h_generator;

  printf("\n[FULL-HYB] %s  m=%zu n=%zu\n", name, m, n);

  blindings = malloc(m * sizeof(*blindings));
  commitments = malloc(m * sizeof(*commitments));
  G_vec = malloc(n * sizeof(*G_vec));
  H_vec = malloc(n * sizeof(*H_vec));

  EXPECT(blindings && commitments && G_vec && H_vec);
  make_context_id(context_id, m);
  EXPECT(secp256k1_mpt_get_h_generator(ctx, &h_generator));

  EXPECT(secp256k1_mpt_get_generator_vector(
      ctx, G_vec, n, (const unsigned char *)"BP_G", 4));
  EXPECT(secp256k1_mpt_get_generator_vector(
      ctx, H_vec, n, (const unsigned char *)"BP_H", 4));

  for (size_t i = 0; i < m; ++i)
  {
    random_scalar(ctx, blindings[i]);
    EXPECT(secp256k1_bulletproof_create_commitment(
        ctx, &commitments[i], values[i], blindings[i], &h_generator));
  }

  for (size_t k3 = 0; k3 <= max_k3; ++k3)
  {
    size_t r3 = 0, r2 = 0, terminal_n = 0;
    size_t proof_len = 0;
    size_t expected_len;
    unsigned char *proof = NULL;
    unsigned char *bad_proof = NULL;

    EXPECT(secp256k1_bulletproof_ipa_hybrid_v1_schedule(
        n, k3, &r3, &r2, &terminal_n));

    expected_len = 228 + 132 * r3 + 66 * r2 + 64 * terminal_n;

    /* Size-query mode must agree with the schedule formula. */
    EXPECT(secp256k1_bulletproof_prove_agg_hybrid_v1(
        ctx, NULL, &proof_len, values,
        (const unsigned char *)blindings, m, k3,
        &h_generator, context_id));
    EXPECT(proof_len == expected_len);

    proof = malloc(proof_len);
    bad_proof = malloc(proof_len);
    EXPECT(proof && bad_proof);

    /* A one-byte-short buffer must be rejected and report required size. */
    if (k3 == 0)
    {
      size_t short_len = proof_len - 1;
      EXPECT(!secp256k1_bulletproof_prove_agg_hybrid_v1(
          ctx, proof, &short_len, values,
          (const unsigned char *)blindings, m, k3,
          &h_generator, context_id));
      EXPECT(short_len == proof_len);
    }

    {
      size_t out_len = proof_len;
      EXPECT(secp256k1_bulletproof_prove_agg_hybrid_v1(
          ctx, proof, &out_len, values,
          (const unsigned char *)blindings, m, k3,
          &h_generator, context_id));
      EXPECT(out_len == proof_len);
    }

    EXPECT(secp256k1_bulletproof_verify_agg_hybrid_v1(
        ctx, G_vec, H_vec, proof, proof_len,
        commitments, m, k3, &h_generator, context_id));

    printf(
        "  H%zu: r3=%zu r2=%zu t=%zu full-bytes=%zu PASSED\n",
        k3, r3, r2, terminal_n, proof_len);

    /* Tamper an active terminal scalar. */
    memcpy(bad_proof, proof, proof_len);
    {
      const size_t terminal_offset =
          4 * 33 + r3 * 4 * 33 + r2 * 2 * 33;
      EXPECT(terminal_offset < proof_len);
      bad_proof[terminal_offset + 31] ^= 0x01u;
    }
    EXPECT(!secp256k1_bulletproof_verify_agg_hybrid_v1(
        ctx, G_vec, H_vec, bad_proof, proof_len,
        commitments, m, k3, &h_generator, context_id));

    /* The full proof remains bound to context_id. */
    {
      unsigned char bad_context[32];
      memcpy(bad_context, context_id, sizeof(bad_context));
      bad_context[0] ^= 0x80u;
      EXPECT(!secp256k1_bulletproof_verify_agg_hybrid_v1(
          ctx, G_vec, H_vec, proof, proof_len,
          commitments, m, k3, &h_generator, bad_context));
    }

    /* The full proof remains bound to the commitment set. */
    {
      secp256k1_pubkey *bad_commitments =
          malloc(m * sizeof(*bad_commitments));
      unsigned char alt_blinding[32];
      EXPECT(bad_commitments != NULL);
      memcpy(bad_commitments, commitments, m * sizeof(*commitments));
      do
      {
        random_scalar(ctx, alt_blinding);
      } while (memcmp(alt_blinding, blindings[m - 1], 32) == 0);
      EXPECT(secp256k1_bulletproof_create_commitment(
          ctx, &bad_commitments[m - 1], values[m - 1],
          alt_blinding, &h_generator));
      EXPECT(!secp256k1_bulletproof_verify_agg_hybrid_v1(
          ctx, G_vec, H_vec, proof, proof_len,
          bad_commitments, m, k3, &h_generator, context_id));
      free(bad_commitments);
    }

    /* A different valid schedule must not verify this proof. */
    if (k3 < max_k3)
    {
      EXPECT(!secp256k1_bulletproof_verify_agg_hybrid_v1(
          ctx, G_vec, H_vec, proof, proof_len,
          commitments, m, k3 + 1, &h_generator, context_id));
    }
    else if (k3 > 0)
    {
      EXPECT(!secp256k1_bulletproof_verify_agg_hybrid_v1(
          ctx, G_vec, H_vec, proof, proof_len,
          commitments, m, k3 - 1, &h_generator, context_id));
    }

    free(proof);
    free(bad_proof);
  }

  /* Noncanonical schedules are rejected by both APIs. */
  {
    size_t bogus_len = 0;
    EXPECT(!secp256k1_bulletproof_prove_agg_hybrid_v1(
        ctx, NULL, &bogus_len, values,
        (const unsigned char *)blindings, m, max_k3 + 1,
        &h_generator, context_id));
  }

  free(blindings);
  free(commitments);
  free(G_vec);
  free(H_vec);
}

int main(void)
{
  secp256k1_context *ctx = secp256k1_context_create(
      SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
  EXPECT(ctx != NULL);

  {
    const uint64_t v[] = {0};
    run_full_hybrid_case(ctx, "single zero", v, 1);
  }

  {
    const uint64_t v[] = {0, 1};
    run_full_hybrid_case(ctx, "two-value aggregate", v, 2);
  }

  {
    const uint64_t v[] = {
        0,
        1,
        UINT64_MAX,
        UINT64_C(0x123456789abcdef0)};
    run_full_hybrid_case(ctx, "four-value aggregate", v, 4);
  }

  secp256k1_context_destroy(ctx);
  printf("\n[SUCCESS] Full aggregated Hybrid-v1 Bulletproof tests passed!\n");
  return 0;
}
