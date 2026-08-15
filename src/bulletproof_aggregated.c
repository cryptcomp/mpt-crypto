/**
 * @file bulletproof_aggregated.c
 * @brief Aggregated Bulletproof Range Proofs (Logarithmic Size).
 *
 * This module implements non-interactive zero-knowledge range proofs based on
 * the Bulletproofs protocol (Bünz et al., 2018). It allows a prover to
 * demonstrate that a committed value lies within the range \f$ [0, 2^{64}) \f$
 * without revealing the value itself.
 *
 * @details
 * **Protocol Overview:**
 * The implementation follows the standard single-value and aggregated
 * Bulletproof logic:
 * 1. **Pedersen Commitment:** The value \f$ v \f$ is committed as \f$ V = v
 * \cdot G + r \cdot H \f$.
 * 2. **Bit Decomposition:** The value is decomposed into 64 bits \f$
 * \mathbf{a}_L \f$.
 * 3. **Polynomial Commitment:** The prover commits to polynomials defining the
 * range constraints.
 * 4. **Inner Product Argument (IPA):** A recursive argument reduces the proof
 * size to logarithmic complexity \f$ \mathcal{O}(\log n) \f$.
 *
 * **Aggregation:**
 * This implementation supports aggregating \f$ m \f$ proofs into a single
 * verification process. The total vector length is \f$ n = 64 \cdot m \f$.
 * Aggregation significantly reduces the on-chain footprint compared to \f$ m
 * \f$ individual proofs.
 *
 * **Fiat-Shamir Transcript:**
 * The non-interactive challenge generation follows a strict dependency chain to
 * ensure binding and special soundness:
 * - \f$ \mathcal{T}_0 \f$: Domain Tag || ContextID || Value Commitments (\f$ V
 * \f$)
 * - \f$ y, z \f$: Derived from \f$ \mathcal{T}_0 \parallel A \parallel S \f$
 * - \f$ x \f$: Derived from \f$ z \parallel T_1 \parallel T_2 \f$
 * - \f$ \mu \f$: Derived from \f$ x \f$ (for the IPA)
 *
 * **Dependencies:**
 * - Relies on `secp256k1` for elliptic curve arithmetic.
 * - Uses `SHA256` for the Fiat-Shamir transformation.
 *
 * @see [Spec (ConfidentialMPT_20260201.pdf) Section 3.3.6 Range Proof (using
 * Bulletproofs)]
 */
#include "mpt_internal.h"
#include "secp256k1_mpt.h"
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <secp256k1.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Bit-size of each value proved in range */
#define BP_VALUE_BITS 64

/* Compute total vector length for aggregated Bulletproof */
#define BP_TOTAL_BITS(m) ((size_t)(BP_VALUE_BITS * (m)))

/* Maximum number of values that can be aggregated in a single proof
 * to prevent excessive memory allocation. */
#define BP_MAX_VALUES 4

/* Compute IPA rounds = log2(total_bits) */
static inline size_t bp_ipa_rounds(size_t total_bits)
{
  size_t r = 0;
  while (total_bits > 1)
  {
    total_bits >>= 1;
    r++;
  }
  return r;
}

/* Compute pure 3-way IPA rounds with dynamic padding.
 * Each round pads the current length to a multiple of 3 and then divides by 3,
 * so the next logical length is ceil(n/3). */
static inline size_t bp_ipa_rounds_3w(size_t total_bits)
{
  size_t r = 0;
  while (total_bits > 1)
  {
    total_bits = (total_bits + 2) / 3;
    r++;
  }
  return r;
}

static inline size_t bp_ipa_padded_len_3w(size_t n)
{
  const size_t rem = n % 3;
  return rem == 0 ? n : n + (3 - rem);
}

/* compute_amount_point is provided by mpt_internal.h.
 * It returns 0 for amount == 0 because libsecp cannot represent the
 * point at infinity.  secp256k1_mpt_pedersen_commit handles the
 * v == 0 case explicitly before reaching this helper. */
/**
 * Safely adds a point to an accumulator (acc += term).
 * Handles uninitialized accumulators by assignment instead of addition.
 */
static int add_term(const secp256k1_context *ctx, secp256k1_pubkey *acc,
                    int *acc_inited, const secp256k1_pubkey *term)
{
  if (!(*acc_inited))
  {
    *acc = *term;
    *acc_inited = 1;
    return 1;
  }
  else
  {
    const secp256k1_pubkey *pts[2] = {acc, term};
    secp256k1_pubkey sum;
    if (!secp256k1_ec_pubkey_combine(ctx, &sum, pts, 2))
      return 0;
    *acc = sum;
    return 1;
  }
}

/**
 * Computes modular subtraction of two scalars: res = a - b (mod q).
 */
static void secp256k1_mpt_scalar_sub(unsigned char *res, const unsigned char *a,
                                     const unsigned char *b)
{
  unsigned char neg_b[kMPT_SCALAR_SIZE];
  memcpy(neg_b, b, kMPT_SCALAR_SIZE);
  secp256k1_mpt_scalar_negate(neg_b, neg_b); /* neg_b = -b mod q */
  secp256k1_mpt_scalar_add(res, a, neg_b);   /* res = a + (-b) */
  OPENSSL_cleanse(neg_b, kMPT_SCALAR_SIZE);
}
/**
 * Computes the modular dot product c = <a, b> = sum(a[i] * b[i]) mod q.
 * This function calculates the inner product of two scalar vectors.
 * ctx       The context.
 * out       Output 32-byte scalar (the inner product result).
 * a         Input scalar vector A (n * 32 bytes).
 * b         Input scalar vector B (n * 32 bytes).
 * n         The length of the vectors.
 * 1 on success, 0 on failure.
 */
int secp256k1_bulletproof_ipa_dot(const secp256k1_context *ctx,
                                  unsigned char *out, const unsigned char *a,
                                  const unsigned char *b, size_t n)
{
  (void)ctx;
  unsigned char acc[kMPT_SCALAR_SIZE] = {0};
  unsigned char term[kMPT_SCALAR_SIZE];

  for (size_t i = 0; i < n; i++)
  {
    secp256k1_mpt_scalar_mul(term, a + i * kMPT_SCALAR_SIZE,
                             b + i * kMPT_SCALAR_SIZE);
    secp256k1_mpt_scalar_add(acc, acc, term);
  }
  memcpy(out, acc, kMPT_SCALAR_SIZE);
  return 1;
}
/**
 * Internal helper for multi-scalar multiplication.
 * Adds a point to the accumulator.
 */

int secp256k1_bulletproof_add_point_to_accumulator(const secp256k1_context *ctx,
                                                   secp256k1_pubkey *acc,
                                                   const secp256k1_pubkey *term)
{
  const secp256k1_pubkey *points[2] = {acc, term};
  secp256k1_pubkey temp_sum;

  if (secp256k1_ec_pubkey_combine(ctx, &temp_sum, points, 2) != 1)
    return 0;
  *acc = temp_sum;
  return 1;
}

static int scalar_is_zero(const unsigned char s[kMPT_SCALAR_SIZE])
{
  unsigned char b = 0;
  for (int i = 0; i < (int)kMPT_SCALAR_SIZE; i++)
  {
    b |= s[i];
  }
  return (b == 0) ? 1 : 0;
}

/**
 * Computes Multiscalar Multiplication (MSM): R = sum(s[i] * P[i]).
 * This function is called in two contexts:
 * 1. secp256k1_bulletproof_ipa_compute_LR (prover only):
 * - Round 0: scalars are a_L/b_R in {0,1}, derived from the prover's secret.
 * - Rounds 1+: scalars are general 256-bit folded values.
 * Timing varies with the scalar's Hamming weight. Because the prover
 * operates on their own secret, exploitation requires an external attacker
 * to have precise timing observation over the prover's local execution
 * environment.
 * 2. fold_generators (verifier) and calculate_commitment_term (prover):
 * Scalars are either public Fiat-Shamir values or sparse bit vectors.
 * There is no secret timing concern in these contexts.
 */

int secp256k1_bulletproof_ipa_msm(const secp256k1_context *ctx,
                                  secp256k1_pubkey *r_out,
                                  const secp256k1_pubkey *points,
                                  const unsigned char *scalars, size_t n)
{
  secp256k1_pubkey acc;
  memset(&acc, 0, sizeof(acc));
  int initialized = 0;

  for (size_t i = 0; i < n; ++i)
  {
    unsigned char s_tmp[kMPT_SCALAR_SIZE];
    memcpy(s_tmp, scalars + i * kMPT_SCALAR_SIZE, kMPT_SCALAR_SIZE);

    if (scalar_is_zero(s_tmp))
    {
      continue;
    }

    secp256k1_pubkey term = points[i];
    if (!mpt_ct_pubkey_tweak_mul(ctx, &term, s_tmp))
      return 0;

    if (!add_term(ctx, &acc, &initialized, &term))
      return 0;
  }

  if (!initialized)
    return 0;

  *r_out = acc;
  return 1;
}

/* Try to add MSM(points, scalars) into acc.
 * If MSM is all-zero, do nothing and succeed.
 */
static int msm_try_add(const secp256k1_context *ctx, secp256k1_pubkey *acc,
                       int *acc_inited, const secp256k1_pubkey *points,
                       const unsigned char *scalars, size_t n)
{
  secp256k1_pubkey tmp;

  /* MSM returns 0 iff all scalars are zero.
   * In that case, we have nothing to add, so we return success (1). */
  if (!secp256k1_bulletproof_ipa_msm(ctx, &tmp, points, scalars, n))
  {
    return 1;
  }
  return add_term(ctx, acc, acc_inited, &tmp);
}

/**
 * Computes component-wise: result[i] = a[i] * b[i] (Hadamard product)
 */
void scalar_vector_mul(const secp256k1_context *ctx,
                       unsigned char res[][kMPT_SCALAR_SIZE],
                       unsigned char a[][kMPT_SCALAR_SIZE],
                       unsigned char b[][kMPT_SCALAR_SIZE], size_t n)
{
  (void)ctx;
  for (size_t i = 0; i < n; i++)
  {
    secp256k1_mpt_scalar_mul(res[i], a[i], b[i]);
  }
}

/**
 * Computes component-wise: result[i] = a[i] + b[i]
 */
void scalar_vector_add(const secp256k1_context *ctx,
                       unsigned char res[][kMPT_SCALAR_SIZE],
                       unsigned char a[][kMPT_SCALAR_SIZE],
                       unsigned char b[][kMPT_SCALAR_SIZE], size_t n)
{
  (void)ctx;
  for (size_t i = 0; i < n; i++)
  {
    secp256k1_mpt_scalar_add(res[i], a[i], b[i]);
  }
}

/**
 * Fills a vector with powers of a scalar: [1, y, y^2, ..., y^{n-1}]
 */
void scalar_vector_powers(const secp256k1_context *ctx,
                          unsigned char res[][kMPT_SCALAR_SIZE],
                          const unsigned char *y, size_t n)
{
  (void)ctx;
  if (n == 0)
    return;

  unsigned char one[kMPT_SCALAR_SIZE] = {0};
  one[kMPT_SCALAR_SIZE - 1] = 1;
  memcpy(res[0], one, kMPT_SCALAR_SIZE);

  for (size_t i = 1; i < n; i++)
  {
    secp256k1_mpt_scalar_mul(res[i], res[i - 1], y);
  }
}
/**
 * Compute y^i for small i.
 */
static void scalar_pow_u32(const secp256k1_context *ctx,
                           unsigned char y_pow_out[kMPT_SCALAR_SIZE],
                           const unsigned char y[kMPT_SCALAR_SIZE],
                           unsigned int i)
{
  (void)ctx;
  unsigned char one[kMPT_SCALAR_SIZE] = {0};
  one[kMPT_SCALAR_SIZE - 1] = 1;
  memcpy(y_pow_out, one, kMPT_SCALAR_SIZE);

  while (i--)
  {
    secp256k1_mpt_scalar_mul(y_pow_out, y_pow_out, y);
  }
}
/**
 * z_j2 = z^(j+2) for j = 0..m-1 (small exponent)
 */
static void
compute_z_pows_j2(const secp256k1_context *ctx,
                  unsigned char (*z_j2)[kMPT_SCALAR_SIZE], /* m x 32 */
                  const unsigned char z[kMPT_SCALAR_SIZE], size_t m)
{
  for (size_t j = 0; j < m; j++)
  {
    scalar_pow_u32(ctx, z_j2[j], z, (unsigned int)(j + 2));
  }
}

/**
 * Computes per-block y-power sums for aggregated Bulletproofs.
 * For block j (0-based):
 *   y_block_sum[j] = sum_{i=0}^{63} y^{64*j + i}
 * Also computes:
 *   two_sum = sum_{i=0}^{63} 2^i
 * These are used by the caller to construct delta(y, z).
 */
static void compute_delta_scalars(
    const secp256k1_context *ctx,
    unsigned char (*y_block_sum)[kMPT_SCALAR_SIZE], /* m blocks */
    unsigned char two_sum[kMPT_SCALAR_SIZE],
    const unsigned char y[kMPT_SCALAR_SIZE], size_t m)
{
  (void)ctx;

  unsigned char one[kMPT_SCALAR_SIZE] = {0};
  unsigned char y_pow[kMPT_SCALAR_SIZE];
  unsigned char two_pow[kMPT_SCALAR_SIZE];

  one[kMPT_SCALAR_SIZE - 1] = 1;

  /* Compute two_sum = sum_{i=0}^{63} 2^i */
  memset(two_sum, 0, kMPT_SCALAR_SIZE);
  memcpy(two_pow, one, kMPT_SCALAR_SIZE);
  for (size_t i = 0; i < 64; i++)
  {
    secp256k1_mpt_scalar_add(two_sum, two_sum, two_pow);
    secp256k1_mpt_scalar_add(two_pow, two_pow, two_pow);
  }

  /* Compute y_block_sum[j] = sum_{i=0}^{63} y^{64j + i} */
  memcpy(y_pow, one, kMPT_SCALAR_SIZE); /* y^0 */

  for (size_t j = 0; j < m; j++)
  {
    memset(y_block_sum[j], 0, kMPT_SCALAR_SIZE);

    for (size_t i = 0; i < 64; i++)
    {
      secp256k1_mpt_scalar_add(y_block_sum[j], y_block_sum[j], y_pow);
      secp256k1_mpt_scalar_mul(y_pow, y_pow, y); /* advance y^k */
    }
  }
}
/**
 * u_flat and uinv_flat are arrays of length (rounds * kMPT_SCALAR_SIZE):
 *   u_j     = u_flat    + 32*j
 *   u_j_inv = uinv_flat + 32*j
 */
int fold_generators(const secp256k1_context *ctx, secp256k1_pubkey *final_point,
                    const secp256k1_pubkey *generators,
                    const unsigned char *u_flat, const unsigned char *uinv_flat,
                    size_t n, size_t rounds,
                    int is_H /* 0 = G folding, 1 = H folding */
)
{
  /* n must be power-of-two and rounds must match log2(n) */
  if (n == 0 || (n & (n - 1)) != 0)
    return 0;
  if (((size_t)1 << rounds) != n)
    return 0;

  /* Allocate scalars for MSM: n * 32 bytes */
  unsigned char *s_flat = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  if (!s_flat)
    return 0;

  unsigned char current_s[kMPT_SCALAR_SIZE];
  int ok = 0;

  for (size_t i = 0; i < n; i++)
  {
    /* current_s = 1 */
    memset(current_s, 0, kMPT_SCALAR_SIZE);
    current_s[31] = 1;

    for (size_t j = 0; j < rounds; j++)
    {
      /* bit from MSB to LSB across 'rounds' bits */
      int bit = (int)((i >> (rounds - 1 - j)) & 1);

      const unsigned char *uj = u_flat + kMPT_SCALAR_SIZE * j;
      const unsigned char *ujinv = uinv_flat + kMPT_SCALAR_SIZE * j;

      if (!is_H)
      {
        /* G folding: bit 0 -> u_inv, bit 1 -> u */
        secp256k1_mpt_scalar_mul(current_s, current_s, bit ? uj : ujinv);
      }
      else
      {
        /* H folding: bit 0 -> u, bit 1 -> u_inv */
        secp256k1_mpt_scalar_mul(current_s, current_s, bit ? ujinv : uj);
      }
    }

    memcpy(s_flat + (i * kMPT_SCALAR_SIZE), current_s, kMPT_SCALAR_SIZE);
  }

  ok = secp256k1_bulletproof_ipa_msm(ctx, final_point, generators, s_flat, n);

  OPENSSL_cleanse(current_s, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(s_flat, n * kMPT_SCALAR_SIZE);
  free(s_flat);

  return ok;
}
/*
 * Apply verifier-side IPA updates to P for `rounds` rounds.
 * Update rule per round i:
 *   P <- P + (u_i^2) * L_i + (u_i^{-2}) * R_i
 * u_flat / uinv_flat are (rounds * kMPT_SCALAR_SIZE)-byte arrays:
 *   u_i    = u_flat    + 32*i
 *   u_iinv = uinv_flat + 32*i
 */
int apply_ipa_folding_to_P(const secp256k1_context *ctx, secp256k1_pubkey *P,
                           const secp256k1_pubkey *L_vec,
                           const secp256k1_pubkey *R_vec,
                           const unsigned char *u_flat,
                           const unsigned char *uinv_flat, size_t rounds)
{
  unsigned char u_sq[kMPT_SCALAR_SIZE], uinv_sq[kMPT_SCALAR_SIZE];
  secp256k1_pubkey tL, tR;
  const secp256k1_pubkey *pts[3];

  for (size_t i = 0; i < rounds; i++)
  {
    const unsigned char *ui = u_flat + kMPT_SCALAR_SIZE * i;
    const unsigned char *uiinv = uinv_flat + kMPT_SCALAR_SIZE * i;

    /* u_sq = u_i^2, uinv_sq = (u_i^{-1})^2 = u_i^{-2} */
    secp256k1_mpt_scalar_mul(u_sq, ui, ui);
    secp256k1_mpt_scalar_mul(uinv_sq, uiinv, uiinv);

    /* tL = (u_i^2) * L_i */
    tL = L_vec[i];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tL, u_sq))
    {
      OPENSSL_cleanse(u_sq, kMPT_SCALAR_SIZE);
      OPENSSL_cleanse(uinv_sq, kMPT_SCALAR_SIZE);
      return 0;
    }

    /* tR = (u_i^{-2}) * R_i */
    tR = R_vec[i];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tR, uinv_sq))
    {
      OPENSSL_cleanse(u_sq, kMPT_SCALAR_SIZE);
      OPENSSL_cleanse(uinv_sq, kMPT_SCALAR_SIZE);
      return 0;
    }

    /* P <- P + tL + tR */
    pts[0] = P;
    pts[1] = &tL;
    pts[2] = &tR;

    secp256k1_pubkey newP;
    if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts, 3))
    {
      OPENSSL_cleanse(u_sq, kMPT_SCALAR_SIZE);
      OPENSSL_cleanse(uinv_sq, kMPT_SCALAR_SIZE);
      return 0;
    }
    *P = newP;
  }

  OPENSSL_cleanse(u_sq, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(uinv_sq, kMPT_SCALAR_SIZE);
  return 1;
}

/**
 * Computes the cross-term commitments L and R.
 * L = <a_L, G_R> + <b_R, H_L> + c_L * ux * g
 * R = <a_R, G_L> + <b_L, H_R> + c_R * ux * g
 * ctx       The context.
 * L         Output: Commitment point L_j.
 * R         Output: Commitment point R_j.
 * half_n    Length of the input vector halves.
 * g         The blinding generator point (Pk_base in our case).
 * return    1 on success, 0 on failure.
 */

int secp256k1_bulletproof_ipa_compute_LR(
    const secp256k1_context *ctx, secp256k1_pubkey *L, secp256k1_pubkey *R,
    const unsigned char *a_L, const unsigned char *a_R,
    const unsigned char *b_L, const unsigned char *b_R,
    const secp256k1_pubkey *G_L, const secp256k1_pubkey *G_R,
    const secp256k1_pubkey *H_L, const secp256k1_pubkey *H_R,
    const secp256k1_pubkey *U, const unsigned char *ux, size_t half_n)
{
  unsigned char cL[kMPT_SCALAR_SIZE], cR[kMPT_SCALAR_SIZE];
  unsigned char cLux[kMPT_SCALAR_SIZE], cRux[kMPT_SCALAR_SIZE];

  secp256k1_pubkey acc, term;
  int acc_inited; /* Tracks if acc contains a valid point */

  /* cL = <a_L, b_R>, cR = <a_R, b_L> */
  if (!secp256k1_bulletproof_ipa_dot(ctx, cL, a_L, b_R, half_n))
    return 0;
  if (!secp256k1_bulletproof_ipa_dot(ctx, cR, a_R, b_L, half_n))
    return 0;

  /* ---------------- L Calculation ---------------- */
  acc_inited = 0;

  /* Try adding terms. correct logic updates acc_inited to 1 */
  if (!msm_try_add(ctx, &acc, &acc_inited, G_R, a_L, half_n))
    goto cleanup;
  if (!msm_try_add(ctx, &acc, &acc_inited, H_L, b_R, half_n))
    goto cleanup;

  secp256k1_mpt_scalar_mul(cLux, cL, ux);
  if (!scalar_is_zero(cLux))
  {
    term = *U;
    if (!mpt_ct_pubkey_tweak_mul(ctx, &term, cLux))
      goto cleanup;
    if (!add_term(ctx, &acc, &acc_inited, &term))
      goto cleanup;
  }

  /* Check initialization explicitly */
  if (acc_inited == 0)
  {
    /* L resulted in Infinity. This is theoretically possible but invalid for
     * serialization. We cannot proceed. */
    goto cleanup;
  }
  *L = acc;

  /* ---------------- R Calculation ---------------- */
  acc_inited = 0;

  if (!msm_try_add(ctx, &acc, &acc_inited, G_L, a_R, half_n))
    goto cleanup;
  if (!msm_try_add(ctx, &acc, &acc_inited, H_R, b_L, half_n))
    goto cleanup;

  secp256k1_mpt_scalar_mul(cRux, cR, ux);
  if (!scalar_is_zero(cRux))
  {
    term = *U;
    if (!mpt_ct_pubkey_tweak_mul(ctx, &term, cRux))
      goto cleanup;
    if (!add_term(ctx, &acc, &acc_inited, &term))
      goto cleanup;
  }

  if (acc_inited == 0)
  {
    goto cleanup;
  }
  *R = acc;

  OPENSSL_cleanse(cL, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cR, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cLux, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cRux, kMPT_SCALAR_SIZE);
  return 1;

cleanup:
  OPENSSL_cleanse(cL, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cR, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cLux, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cRux, kMPT_SCALAR_SIZE);
  return 0;
}
/**
 * One IPA compression step (in-place).
 *
 * Input vectors are length (2*half_n):
 *   a[0..2*half_n-1], b[0..2*half_n-1],
 *   G[0..2*half_n-1], H[0..2*half_n-1]
 *
 * After return, the first half contains folded vectors:
 *   a'[0..half_n-1], b'[0..half_n-1], G'[0..half_n-1], H'[0..half_n-1]
 *
 * Formulas (matching prover/verifier conventions):
 *   a'[i] = aL[i]*x + aR[i]*x_inv
 *   b'[i] = bL[i]*x_inv + bR[i]*x
 *   G'[i] = GL[i]*x_inv + GR[i]*x
 *   H'[i] = HL[i]*x + HR[i]*x_inv
 */
int secp256k1_bulletproof_ipa_compress_step(const secp256k1_context *ctx,
                                            unsigned char *a, unsigned char *b,
                                            secp256k1_pubkey *G,
                                            secp256k1_pubkey *H, size_t half_n,
                                            const unsigned char *x,
                                            const unsigned char *x_inv)
{
  size_t i;
  int ok = 0;

  unsigned char t1[kMPT_SCALAR_SIZE], t2[kMPT_SCALAR_SIZE];
  secp256k1_pubkey left, right;
  const secp256k1_pubkey *pts[2];

  if (ctx == NULL || a == NULL || b == NULL || G == NULL || H == NULL)
    return 0;
  if (half_n == 0)
    return 0;

  /* x and x_inv must be valid non-zero scalars */
  if (secp256k1_ec_seckey_verify(ctx, x) != 1)
    return 0;
  if (secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
    return 0;

  for (i = 0; i < half_n; ++i)
  {
    unsigned char *aL = a + (i * kMPT_SCALAR_SIZE);
    unsigned char *aR = a + ((i + half_n) * kMPT_SCALAR_SIZE);

    unsigned char *bL = b + (i * kMPT_SCALAR_SIZE);
    unsigned char *bR = b + ((i + half_n) * kMPT_SCALAR_SIZE);

    /* a'[i] = aL*x + aR*x_inv */
    secp256k1_mpt_scalar_mul(t1, aL, x);
    secp256k1_mpt_scalar_mul(t2, aR, x_inv);
    secp256k1_mpt_scalar_add(aL, t1, t2);

    /* b'[i] = bL*x_inv + bR*x */
    secp256k1_mpt_scalar_mul(t1, bL, x_inv);
    secp256k1_mpt_scalar_mul(t2, bR, x);
    secp256k1_mpt_scalar_add(bL, t1, t2);

    /* G'[i] = GL*x_inv + GR*x */
    left = G[i];
    right = G[i + half_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &left, x_inv))
      goto cleanup;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &right, x))
      goto cleanup;
    pts[0] = &left;
    pts[1] = &right;
    if (!secp256k1_ec_pubkey_combine(ctx, &G[i], pts, 2))
      goto cleanup;

    /* H'[i] = HL*x + HR*x_inv */
    left = H[i];
    right = H[i + half_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &left, x))
      goto cleanup;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &right, x_inv))
      goto cleanup;
    pts[0] = &left;
    pts[1] = &right;
    if (!secp256k1_ec_pubkey_combine(ctx, &H[i], pts, 2))
      goto cleanup;
  }

  ok = 1;

cleanup:
  OPENSSL_cleanse(t1, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(t2, kMPT_SCALAR_SIZE);
  return ok;
}

/*
 * ux is the fixed IPA binding scalar.
 *
 * It MUST be derived exactly once from:
 *     ux = H(commit_inp || <a,b>)
 *
 * and reused consistently throughout the IPA:
 *   - L/R cross-term construction
 *   - final (a·b·ux)·g term
 *
 * It MUST NOT depend on per-round challenges (u_i),
 * and MUST be identical for prover and verifier.
 */
int derive_ipa_binding_challenge(const secp256k1_context *ctx,
                                 unsigned char *ux_out,
                                 const unsigned char *commit_inp_32,
                                 const unsigned char *dot_32)
{
  unsigned char hash_input[2 * kMPT_SCALAR_SIZE];
  unsigned char hash_output[kMPT_HALF_SHA_SIZE];
  EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
  int ok = 0;

  if (!mdctx)
    return 0;

  /* 1. Build hash input = commit_inp || dot */
  memcpy(hash_input, commit_inp_32, kMPT_SCALAR_SIZE);
  memcpy(hash_input + kMPT_SCALAR_SIZE, dot_32, kMPT_SCALAR_SIZE);

  /* 2. Hash */
  if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    goto cleanup;
  if (EVP_DigestUpdate(mdctx, hash_input, 2 * kMPT_SCALAR_SIZE) != 1)
    goto cleanup;
  if (EVP_DigestFinal_ex(mdctx, hash_output, NULL) != 1)
    goto cleanup;

  /* 3. Reduce hash to a valid scalar */
  secp256k1_mpt_scalar_reduce32(ux_out, hash_output);

  /* 4. Verify (Sanity check) */
  if (secp256k1_ec_seckey_verify(ctx, ux_out) != 1)
    goto cleanup;

  ok = 1;

cleanup:
  EVP_MD_CTX_free(mdctx);
  return ok;
}

/**
 * Derive u = H(last_challenge || L || R) reduced to a valid scalar.
 * IMPORTANT: use the SAME exact logic in verifier.
 */

int derive_ipa_round_challenge(
    const secp256k1_context *ctx, unsigned char u_out[kMPT_SCALAR_SIZE],
    const unsigned char last_challenge[kMPT_SCALAR_SIZE],
    const secp256k1_pubkey *L, const secp256k1_pubkey *R)
{
  unsigned char L_ser[kMPT_PUBKEY_SIZE], R_ser[kMPT_PUBKEY_SIZE];
  size_t len;
  unsigned char hash[kMPT_HALF_SHA_SIZE];
  EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
  int ok = 0;

  if (!mdctx)
    return 0;

  len = kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_serialize(ctx, L_ser, &len, L,
                                     SECP256K1_EC_COMPRESSED) ||
      len != kMPT_PUBKEY_SIZE)
    goto cleanup;

  len = kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_serialize(ctx, R_ser, &len, R,
                                     SECP256K1_EC_COMPRESSED) ||
      len != kMPT_PUBKEY_SIZE)
    goto cleanup;

  if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    goto cleanup;
  if (EVP_DigestUpdate(mdctx, last_challenge, kMPT_SCALAR_SIZE) != 1)
    goto cleanup;
  if (EVP_DigestUpdate(mdctx, L_ser, kMPT_PUBKEY_SIZE) != 1)
    goto cleanup;
  if (EVP_DigestUpdate(mdctx, R_ser, kMPT_PUBKEY_SIZE) != 1)
    goto cleanup;
  if (EVP_DigestFinal_ex(mdctx, hash, NULL) != 1)
    goto cleanup;

  secp256k1_mpt_scalar_reduce32(hash, hash);
  memcpy(u_out, hash, kMPT_SCALAR_SIZE);

  if (secp256k1_ec_seckey_verify(ctx, u_out) != 1)
    goto cleanup;

  ok = 1;

cleanup:
  EVP_MD_CTX_free(mdctx);
  return ok;
}

/*
 * Compute a binding digest of the BP fixed generators:
 *   gens_digest = SHA256( H || G_vec[0..n-1] || H_vec[0..n-1] )
 *
 * This 32-byte digest is included in the Fiat-Shamir transcript T_0 so the
 * challenges (y, z) bind to the exact generator set the prover used.  Per
 * the spec (CMPT appendix.tex, "Fiat-Shamir Challenges", T_0 definition),
 * T_0 includes the fixed BP generators (G, H, G, H); this implementation
 * folds them down to a single 32-byte digest absorbed into T_0 once,
 * giving the same binding at constant per-proof transcript cost.
 *
 * Note: in this implementation the value-commitment base "G" is G_vec[0],
 * so it is implicitly included via the G_vec sweep below.
 */
static int bulletproof_gens_digest(const secp256k1_context *ctx,
                                   const secp256k1_pubkey *pk_base,
                                   const secp256k1_pubkey *G_vec,
                                   const secp256k1_pubkey *H_vec, size_t n,
                                   unsigned char out[32])
{
  EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
  unsigned char buf[33];
  size_t len;
  int ok = 0;

  if (!mdctx)
    return 0;

  if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    goto done;

  /* H base used for blinding in the Pedersen commitment. */
  len = 33;
  if (!secp256k1_ec_pubkey_serialize(ctx, buf, &len, pk_base,
                                     SECP256K1_EC_COMPRESSED) ||
      len != 33)
    goto done;
  if (EVP_DigestUpdate(mdctx, buf, 33) != 1)
    goto done;

  /* G_vec (length n).  G_vec[0] doubles as the value-commitment base G. */
  for (size_t i = 0; i < n; i++)
  {
    len = 33;
    if (!secp256k1_ec_pubkey_serialize(ctx, buf, &len, &G_vec[i],
                                       SECP256K1_EC_COMPRESSED) ||
        len != 33)
      goto done;
    if (EVP_DigestUpdate(mdctx, buf, 33) != 1)
      goto done;
  }

  /* H_vec (length n). */
  for (size_t i = 0; i < n; i++)
  {
    len = 33;
    if (!secp256k1_ec_pubkey_serialize(ctx, buf, &len, &H_vec[i],
                                       SECP256K1_EC_COMPRESSED) ||
        len != 33)
      goto done;
    if (EVP_DigestUpdate(mdctx, buf, 33) != 1)
      goto done;
  }

  if (EVP_DigestFinal_ex(mdctx, out, NULL) != 1)
    goto done;

  ok = 1;
done:
  EVP_MD_CTX_free(mdctx);
  return ok;
}

/* Encode x as a 4-byte big-endian unsigned integer. */
static void bulletproof_be32_encode(unsigned char out[4], uint32_t x)
{
  out[0] = (unsigned char)((x >> 24) & 0xFF);
  out[1] = (unsigned char)((x >> 16) & 0xFF);
  out[2] = (unsigned char)((x >> 8) & 0xFF);
  out[3] = (unsigned char)(x & 0xFF);
}


/* ==========================================================================\n * Pure 3-way Inner Product Argument with dynamic per-round zero padding.\n *\n * A 3-way round extends the current vectors with 0 coordinates until the\n * length is divisible by 3, splits them as (1,2,3), sends four cross\n * commitments L1,L2,R1,R2, and folds 3 -> 1 using a single challenge x.\n *\n * The algebra follows Algorithm 1 of the 3-way IPA construction:\n *   a' = x a1 + a2 + x^{-1} a3\n *   b' = x^{-1} b1 + b2 + x b3\n *   G' = x^{-1} G1 + G2 + x G3\n *   H' = x H1 + H2 + x^{-1} H3\n *\n * Verifier point update:\n *   P' = P + x L1 + x^2 L2 + x^{-1} R1 + x^{-2} R2.\n * ========================================================================== */

static int scalar_vector_all_zero_3w(const unsigned char *scalars, size_t n)
{
  for (size_t i = 0; i < n; i++)
  {
    if (!scalar_is_zero(scalars + i * kMPT_SCALAR_SIZE))
      return 0;
  }
  return 1;
}

/* Accept canonical field scalars, including zero.  libsecp's seckey verifier
 * is not suitable for proof scalars because it rejects zero. */
static int scalar_is_canonical_3w(const unsigned char s[kMPT_SCALAR_SIZE])
{
  unsigned char reduced[kMPT_SCALAR_SIZE];
  secp256k1_mpt_scalar_reduce32(reduced, s);
  int ok = (CRYPTO_memcmp(reduced, s, kMPT_SCALAR_SIZE) == 0);
  OPENSSL_cleanse(reduced, kMPT_SCALAR_SIZE);
  return ok;
}

/* Add MSM(points, scalars) to acc.  An all-zero scalar vector contributes the
 * identity and is skipped; any MSM failure for a non-zero vector is fatal. */
static int msm_add_checked_3w(const secp256k1_context *ctx,
                              secp256k1_pubkey *acc, int *acc_inited,
                              const secp256k1_pubkey *points,
                              const unsigned char *scalars, size_t n)
{
  secp256k1_pubkey tmp;
  if (scalar_vector_all_zero_3w(scalars, n))
    return 1;
  if (!secp256k1_bulletproof_ipa_msm(ctx, &tmp, points, scalars, n))
    return 0;
  return add_term(ctx, acc, acc_inited, &tmp);
}

static int add_scaled_U_term_3w(const secp256k1_context *ctx,
                                secp256k1_pubkey *acc, int *acc_inited,
                                const secp256k1_pubkey *U,
                                const unsigned char c[kMPT_SCALAR_SIZE],
                                const unsigned char ux[kMPT_SCALAR_SIZE])
{
  unsigned char cux[kMPT_SCALAR_SIZE];
  secp256k1_pubkey term;
  int ok = 0;

  secp256k1_mpt_scalar_mul(cux, c, ux);
  if (scalar_is_zero(cux))
  {
    ok = 1;
    goto cleanup;
  }

  term = *U;
  if (!mpt_ct_pubkey_tweak_mul(ctx, &term, cux))
    goto cleanup;
  if (!add_term(ctx, acc, acc_inited, &term))
    goto cleanup;

  ok = 1;
cleanup:
  OPENSSL_cleanse(cux, kMPT_SCALAR_SIZE);
  return ok;
}

/* Deterministically derive the independent generators used only for zero
 * coordinates introduced by dynamic padding.  The labels bind the original
 * IPA dimension and the recursion round, and G/H use separate domains. */
static int derive_ipa_pad_generators_3w(
    const secp256k1_context *ctx, secp256k1_pubkey *G_pad,
    secp256k1_pubkey *H_pad, size_t pad_count, size_t original_n,
    size_t round_index)
{
  static const unsigned char g_prefix[] = "BP_3W_PAD_G";
  static const unsigned char h_prefix[] = "BP_3W_PAD_H";
  unsigned char g_label[(sizeof(g_prefix) - 1) + 8];
  unsigned char h_label[(sizeof(h_prefix) - 1) + 8];
  const size_t prefix_len = sizeof(g_prefix) - 1;

  if (pad_count == 0)
    return 1;
  if (pad_count > 2 || original_n > UINT32_MAX || round_index > UINT32_MAX)
    return 0;

  memcpy(g_label, g_prefix, prefix_len);
  memcpy(h_label, h_prefix, prefix_len);
  bulletproof_be32_encode(g_label + prefix_len, (uint32_t)original_n);
  bulletproof_be32_encode(h_label + prefix_len, (uint32_t)original_n);
  bulletproof_be32_encode(g_label + prefix_len + 4, (uint32_t)round_index);
  bulletproof_be32_encode(h_label + prefix_len + 4, (uint32_t)round_index);

  if (!secp256k1_mpt_get_generator_vector(ctx, G_pad, pad_count, g_label,
                                          sizeof(g_label)))
    return 0;
  if (!secp256k1_mpt_get_generator_vector(ctx, H_pad, pad_count, h_label,
                                          sizeof(h_label)))
    return 0;
  return 1;
}

/* Compute the four cross-term commitments for one 3-way round. */
static int secp256k1_bulletproof_ipa_compute_LR_3w(
    const secp256k1_context *ctx, secp256k1_pubkey *L1,
    secp256k1_pubkey *L2, secp256k1_pubkey *R1, secp256k1_pubkey *R2,
    const unsigned char *a, const unsigned char *b,
    const secp256k1_pubkey *G, const secp256k1_pubkey *H,
    const secp256k1_pubkey *U, const unsigned char *ux, size_t third_n)
{
  const size_t s = third_n * kMPT_SCALAR_SIZE;
  const unsigned char *a1 = a;
  const unsigned char *a2 = a + s;
  const unsigned char *a3 = a + 2 * s;
  const unsigned char *b1 = b;
  const unsigned char *b2 = b + s;
  const unsigned char *b3 = b + 2 * s;
  const secp256k1_pubkey *G1 = G;
  const secp256k1_pubkey *G2 = G + third_n;
  const secp256k1_pubkey *G3 = G + 2 * third_n;
  const secp256k1_pubkey *H1 = H;
  const secp256k1_pubkey *H2 = H + third_n;
  const secp256k1_pubkey *H3 = H + 2 * third_n;

  unsigned char cL1[kMPT_SCALAR_SIZE], cL2[kMPT_SCALAR_SIZE];
  unsigned char cR1[kMPT_SCALAR_SIZE], cR2[kMPT_SCALAR_SIZE];
  unsigned char d1[kMPT_SCALAR_SIZE], d2[kMPT_SCALAR_SIZE];
  secp256k1_pubkey acc;
  int inited = 0;
  int ok = 0;

  /* cL1 = <a1,b2> + <a2,b3> */
  if (!secp256k1_bulletproof_ipa_dot(ctx, d1, a1, b2, third_n) ||
      !secp256k1_bulletproof_ipa_dot(ctx, d2, a2, b3, third_n))
    goto cleanup;
  secp256k1_mpt_scalar_add(cL1, d1, d2);

  /* cL2 = <a1,b3> */
  if (!secp256k1_bulletproof_ipa_dot(ctx, cL2, a1, b3, third_n))
    goto cleanup;

  /* cR1 = <a2,b1> + <a3,b2> */
  if (!secp256k1_bulletproof_ipa_dot(ctx, d1, a2, b1, third_n) ||
      !secp256k1_bulletproof_ipa_dot(ctx, d2, a3, b2, third_n))
    goto cleanup;
  secp256k1_mpt_scalar_add(cR1, d1, d2);

  /* cR2 = <a3,b1> */
  if (!secp256k1_bulletproof_ipa_dot(ctx, cR2, a3, b1, third_n))
    goto cleanup;

  /* L1 = <a1,G2> + <a2,G3> + <b2,H1> + <b3,H2> + ux*cL1*U */
  inited = 0;
  if (!msm_add_checked_3w(ctx, &acc, &inited, G2, a1, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, G3, a2, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, H1, b2, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, H2, b3, third_n) ||
      !add_scaled_U_term_3w(ctx, &acc, &inited, U, cL1, ux) || !inited)
    goto cleanup;
  *L1 = acc;

  /* L2 = <a1,G3> + <b3,H1> + ux*cL2*U */
  inited = 0;
  if (!msm_add_checked_3w(ctx, &acc, &inited, G3, a1, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, H1, b3, third_n) ||
      !add_scaled_U_term_3w(ctx, &acc, &inited, U, cL2, ux) || !inited)
    goto cleanup;
  *L2 = acc;

  /* R1 = <a2,G1> + <a3,G2> + <b1,H2> + <b2,H3> + ux*cR1*U */
  inited = 0;
  if (!msm_add_checked_3w(ctx, &acc, &inited, G1, a2, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, G2, a3, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, H2, b1, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, H3, b2, third_n) ||
      !add_scaled_U_term_3w(ctx, &acc, &inited, U, cR1, ux) || !inited)
    goto cleanup;
  *R1 = acc;

  /* R2 = <a3,G1> + <b1,H3> + ux*cR2*U */
  inited = 0;
  if (!msm_add_checked_3w(ctx, &acc, &inited, G1, a3, third_n) ||
      !msm_add_checked_3w(ctx, &acc, &inited, H3, b1, third_n) ||
      !add_scaled_U_term_3w(ctx, &acc, &inited, U, cR2, ux) || !inited)
    goto cleanup;
  *R2 = acc;

  ok = 1;
cleanup:
  OPENSSL_cleanse(cL1, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cL2, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cR1, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(cR2, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(d1, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(d2, kMPT_SCALAR_SIZE);
  return ok;
}

/* Fiat-Shamir challenge for one 3W round. */
static int derive_ipa_round_challenge_3w(
    const secp256k1_context *ctx, unsigned char x_out[kMPT_SCALAR_SIZE],
    const unsigned char last_challenge[kMPT_SCALAR_SIZE],
    const secp256k1_pubkey *L1, const secp256k1_pubkey *L2,
    const secp256k1_pubkey *R1, const secp256k1_pubkey *R2)
{
  static const unsigned char domain[] = "MPT_BP_IPA_3W_ROUND";
  const secp256k1_pubkey *pts[4] = {L1, L2, R1, R2};
  unsigned char ser[4][kMPT_PUBKEY_SIZE];
  unsigned char hash[kMPT_HALF_SHA_SIZE];
  EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
  int ok = 0;

  if (!mdctx)
    return 0;

  for (size_t i = 0; i < 4; i++)
  {
    size_t len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, ser[i], &len, pts[i],
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto cleanup;
  }

  if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1 ||
      EVP_DigestUpdate(mdctx, domain, sizeof(domain) - 1) != 1 ||
      EVP_DigestUpdate(mdctx, last_challenge, kMPT_SCALAR_SIZE) != 1)
    goto cleanup;
  for (size_t i = 0; i < 4; i++)
  {
    if (EVP_DigestUpdate(mdctx, ser[i], kMPT_PUBKEY_SIZE) != 1)
      goto cleanup;
  }
  if (EVP_DigestFinal_ex(mdctx, hash, NULL) != 1)
    goto cleanup;

  secp256k1_mpt_scalar_reduce32(x_out, hash);
  if (secp256k1_ec_seckey_verify(ctx, x_out) != 1)
    goto cleanup; /* challenge must be non-zero */

  ok = 1;
cleanup:
  OPENSSL_cleanse(hash, sizeof(hash));
  OPENSSL_cleanse(ser, sizeof(ser));
  EVP_MD_CTX_free(mdctx);
  return ok;
}

/* Fold a,b,G,H in-place for one already-padded 3W round. */
static int secp256k1_bulletproof_ipa_compress_step_3w(
    const secp256k1_context *ctx, unsigned char *a, unsigned char *b,
    secp256k1_pubkey *G, secp256k1_pubkey *H, size_t third_n,
    const unsigned char *x, const unsigned char *x_inv)
{
  unsigned char t1[kMPT_SCALAR_SIZE], t2[kMPT_SCALAR_SIZE];
  secp256k1_pubkey p1, p2, p3;
  const secp256k1_pubkey *pts[3];
  int ok = 0;

  if (!ctx || !a || !b || !G || !H || third_n == 0)
    return 0;
  if (secp256k1_ec_seckey_verify(ctx, x) != 1 ||
      secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
    return 0;

  for (size_t i = 0; i < third_n; i++)
  {
    unsigned char *a1 = a + i * kMPT_SCALAR_SIZE;
    unsigned char *a2 = a + (i + third_n) * kMPT_SCALAR_SIZE;
    unsigned char *a3 = a + (i + 2 * third_n) * kMPT_SCALAR_SIZE;
    unsigned char *b1 = b + i * kMPT_SCALAR_SIZE;
    unsigned char *b2 = b + (i + third_n) * kMPT_SCALAR_SIZE;
    unsigned char *b3 = b + (i + 2 * third_n) * kMPT_SCALAR_SIZE;

    /* a' = x*a1 + a2 + x^{-1}*a3 */
    secp256k1_mpt_scalar_mul(t1, a1, x);
    secp256k1_mpt_scalar_mul(t2, a3, x_inv);
    secp256k1_mpt_scalar_add(t1, t1, a2);
    secp256k1_mpt_scalar_add(a1, t1, t2);

    /* b' = x^{-1}*b1 + b2 + x*b3 */
    secp256k1_mpt_scalar_mul(t1, b1, x_inv);
    secp256k1_mpt_scalar_mul(t2, b3, x);
    secp256k1_mpt_scalar_add(t1, t1, b2);
    secp256k1_mpt_scalar_add(b1, t1, t2);

    /* G' = x^{-1}*G1 + G2 + x*G3 */
    p1 = G[i];
    p2 = G[i + third_n];
    p3 = G[i + 2 * third_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &p1, x_inv) ||
        !secp256k1_ec_pubkey_tweak_mul(ctx, &p3, x))
      goto cleanup;
    pts[0] = &p1;
    pts[1] = &p2;
    pts[2] = &p3;
    if (!secp256k1_ec_pubkey_combine(ctx, &G[i], pts, 3))
      goto cleanup;

    /* H' = x*H1 + H2 + x^{-1}*H3 */
    p1 = H[i];
    p2 = H[i + third_n];
    p3 = H[i + 2 * third_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &p1, x) ||
        !secp256k1_ec_pubkey_tweak_mul(ctx, &p3, x_inv))
      goto cleanup;
    pts[0] = &p1;
    pts[1] = &p2;
    pts[2] = &p3;
    if (!secp256k1_ec_pubkey_combine(ctx, &H[i], pts, 3))
      goto cleanup;
  }

  ok = 1;
cleanup:
  OPENSSL_cleanse(t1, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(t2, kMPT_SCALAR_SIZE);
  return ok;
}

/* Verifier-only generator folding for one already-padded 3W round. */
static int fold_generators_step_3w(const secp256k1_context *ctx,
                                   secp256k1_pubkey *G,
                                   secp256k1_pubkey *H, size_t third_n,
                                   const unsigned char *x,
                                   const unsigned char *x_inv)
{
  secp256k1_pubkey p1, p2, p3;
  const secp256k1_pubkey *pts[3];

  for (size_t i = 0; i < third_n; i++)
  {
    p1 = G[i];
    p2 = G[i + third_n];
    p3 = G[i + 2 * third_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &p1, x_inv) ||
        !secp256k1_ec_pubkey_tweak_mul(ctx, &p3, x))
      return 0;
    pts[0] = &p1;
    pts[1] = &p2;
    pts[2] = &p3;
    if (!secp256k1_ec_pubkey_combine(ctx, &G[i], pts, 3))
      return 0;

    p1 = H[i];
    p2 = H[i + third_n];
    p3 = H[i + 2 * third_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &p1, x) ||
        !secp256k1_ec_pubkey_tweak_mul(ctx, &p3, x_inv))
      return 0;
    pts[0] = &p1;
    pts[1] = &p2;
    pts[2] = &p3;
    if (!secp256k1_ec_pubkey_combine(ctx, &H[i], pts, 3))
      return 0;
  }
  return 1;
}

/* P <- P + x*L1 + x^2*L2 + x^{-1}*R1 + x^{-2}*R2. */
static int apply_ipa_folding_to_P_3w(
    const secp256k1_context *ctx, secp256k1_pubkey *P,
    const secp256k1_pubkey *L1, const secp256k1_pubkey *L2,
    const secp256k1_pubkey *R1, const secp256k1_pubkey *R2,
    const unsigned char *x, const unsigned char *x_inv)
{
  unsigned char x_sq[kMPT_SCALAR_SIZE], x_inv_sq[kMPT_SCALAR_SIZE];
  secp256k1_pubkey tL1 = *L1, tL2 = *L2, tR1 = *R1, tR2 = *R2, newP;
  const secp256k1_pubkey *pts[5];
  int ok = 0;

  secp256k1_mpt_scalar_mul(x_sq, x, x);
  secp256k1_mpt_scalar_mul(x_inv_sq, x_inv, x_inv);

  if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tL1, x) ||
      !secp256k1_ec_pubkey_tweak_mul(ctx, &tL2, x_sq) ||
      !secp256k1_ec_pubkey_tweak_mul(ctx, &tR1, x_inv) ||
      !secp256k1_ec_pubkey_tweak_mul(ctx, &tR2, x_inv_sq))
    goto cleanup;

  pts[0] = P;
  pts[1] = &tL1;
  pts[2] = &tL2;
  pts[3] = &tR1;
  pts[4] = &tR2;
  if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts, 5))
    goto cleanup;
  *P = newP;
  ok = 1;

cleanup:
  OPENSSL_cleanse(x_sq, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(x_inv_sq, kMPT_SCALAR_SIZE);
  return ok;
}

/* Pure 3W prover.  Inputs are copied because dynamic padding requires up to
 * two extra slots in the first round and the caller's original vectors should
 * remain unchanged. */
int secp256k1_bulletproof_run_ipa_prover_3w(
    const secp256k1_context *ctx, const secp256k1_pubkey *U,
    const secp256k1_pubkey *G_vec, const secp256k1_pubkey *H_vec,
    const unsigned char *a_vec, const unsigned char *b_vec, size_t n,
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE],
    const unsigned char ux_scalar[kMPT_SCALAR_SIZE],
    secp256k1_pubkey *L1_out, secp256k1_pubkey *L2_out,
    secp256k1_pubkey *R1_out, secp256k1_pubkey *R2_out, size_t max_rounds,
    size_t *rounds_out, unsigned char a_final[kMPT_SCALAR_SIZE],
    unsigned char b_final[kMPT_SCALAR_SIZE])
{
  const size_t rounds = bp_ipa_rounds_3w(n);
  const size_t capacity = n + 2;
  secp256k1_pubkey *Gw = NULL, *Hw = NULL;
  unsigned char *aw = NULL, *bw = NULL;
  unsigned char x[kMPT_SCALAR_SIZE], x_inv[kMPT_SCALAR_SIZE];
  unsigned char last[kMPT_SCALAR_SIZE];
  size_t cur_n = n;
  int ok = 0;

  if (!ctx || !U || !G_vec || !H_vec || !a_vec || !b_vec || n == 0 ||
      rounds > max_rounds)
    return 0;

  Gw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  Hw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  aw = (unsigned char *)malloc(capacity * kMPT_SCALAR_SIZE);
  bw = (unsigned char *)malloc(capacity * kMPT_SCALAR_SIZE);
  if (!Gw || !Hw || !aw || !bw)
    goto cleanup;

  memcpy(Gw, G_vec, n * sizeof(secp256k1_pubkey));
  memcpy(Hw, H_vec, n * sizeof(secp256k1_pubkey));
  memcpy(aw, a_vec, n * kMPT_SCALAR_SIZE);
  memcpy(bw, b_vec, n * kMPT_SCALAR_SIZE);
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);

  for (size_t r = 0; r < rounds; r++)
  {
    const size_t padded_n = bp_ipa_padded_len_3w(cur_n);
    const size_t pad = padded_n - cur_n;
    const size_t third_n = padded_n / 3;

    if (padded_n > capacity)
      goto cleanup;

    if (pad)
    {
      memset(aw + cur_n * kMPT_SCALAR_SIZE, 0, pad * kMPT_SCALAR_SIZE);
      memset(bw + cur_n * kMPT_SCALAR_SIZE, 0, pad * kMPT_SCALAR_SIZE);
      if (!derive_ipa_pad_generators_3w(ctx, Gw + cur_n, Hw + cur_n, pad, n,
                                        r))
        goto cleanup;
    }

    if (!secp256k1_bulletproof_ipa_compute_LR_3w(
            ctx, &L1_out[r], &L2_out[r], &R1_out[r], &R2_out[r], aw, bw, Gw,
            Hw, U, ux_scalar, third_n))
      goto cleanup;

    if (!derive_ipa_round_challenge_3w(ctx, x, last, &L1_out[r], &L2_out[r],
                                       &R1_out[r], &R2_out[r]))
      goto cleanup;
    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    if (!secp256k1_bulletproof_ipa_compress_step_3w(ctx, aw, bw, Gw, Hw,
                                                    third_n, x, x_inv))
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
    cur_n = third_n;
  }

  if (cur_n != 1)
    goto cleanup;
  memcpy(a_final, aw, kMPT_SCALAR_SIZE);
  memcpy(b_final, bw, kMPT_SCALAR_SIZE);
  if (rounds_out)
    *rounds_out = rounds;
  ok = 1;

cleanup:
  OPENSSL_cleanse(x, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(x_inv, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(last, kMPT_SCALAR_SIZE);
  if (aw)
    OPENSSL_cleanse(aw, capacity * kMPT_SCALAR_SIZE);
  if (bw)
    OPENSSL_cleanse(bw, capacity * kMPT_SCALAR_SIZE);
  if (Gw)
    OPENSSL_cleanse(Gw, capacity * sizeof(secp256k1_pubkey));
  if (Hw)
    OPENSSL_cleanse(Hw, capacity * sizeof(secp256k1_pubkey));
  free(aw);
  free(bw);
  free(Gw);
  free(Hw);
  return ok;
}

/* Explicit verifier for pure 3W.  This intentionally performs the generator
 * folds round-by-round.  It is the simplest correctness baseline; a later
 * optimization can collapse the verification into one MSM. */
int ipa_verify_explicit_3w(
    const secp256k1_context *ctx, const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec, const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in, const secp256k1_pubkey *L1_vec,
    const secp256k1_pubkey *L2_vec, const secp256k1_pubkey *R1_vec,
    const secp256k1_pubkey *R2_vec, size_t n,
    const unsigned char a_final[kMPT_SCALAR_SIZE],
    const unsigned char b_final[kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  const size_t rounds = bp_ipa_rounds_3w(n);
  const size_t capacity = n + 2;
  secp256k1_pubkey *Gw = NULL, *Hw = NULL;
  secp256k1_pubkey P = *P_in, RHS, tmp;
  unsigned char x[kMPT_SCALAR_SIZE], x_inv[kMPT_SCALAR_SIZE];
  unsigned char last[kMPT_SCALAR_SIZE];
  size_t cur_n = n;
  int RHS_inited = 0;
  int ok = 0;

  Gw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  Hw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  if (!Gw || !Hw)
    goto cleanup;

  memcpy(Gw, G_vec, n * sizeof(secp256k1_pubkey));
  memcpy(Hw, H_vec, n * sizeof(secp256k1_pubkey));
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);

  for (size_t r = 0; r < rounds; r++)
  {
    const size_t padded_n = bp_ipa_padded_len_3w(cur_n);
    const size_t pad = padded_n - cur_n;
    const size_t third_n = padded_n / 3;

    if (!derive_ipa_round_challenge_3w(ctx, x, last, &L1_vec[r], &L2_vec[r],
                                       &R1_vec[r], &R2_vec[r]))
      goto cleanup;
    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    if (!apply_ipa_folding_to_P_3w(ctx, &P, &L1_vec[r], &L2_vec[r],
                                   &R1_vec[r], &R2_vec[r], x, x_inv))
      goto cleanup;

    if (pad &&
        !derive_ipa_pad_generators_3w(ctx, Gw + cur_n, Hw + cur_n, pad, n, r))
      goto cleanup;

    if (!fold_generators_step_3w(ctx, Gw, Hw, third_n, x, x_inv))
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
    cur_n = third_n;
  }

  if (cur_n != 1)
    goto cleanup;

  /* RHS = a*Gf + b*Hf + (a*b*ux)*U */
  if (!scalar_is_zero(a_final))
  {
    tmp = Gw[0];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, a_final) ||
        !add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }
  if (!scalar_is_zero(b_final))
  {
    tmp = Hw[0];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, b_final) ||
        !add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }
  {
    unsigned char ab[kMPT_SCALAR_SIZE], abux[kMPT_SCALAR_SIZE];
    secp256k1_mpt_scalar_mul(ab, a_final, b_final);
    secp256k1_mpt_scalar_mul(abux, ab, ux);
    if (!scalar_is_zero(abux))
    {
      tmp = *U;
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, abux) ||
          !add_term(ctx, &RHS, &RHS_inited, &tmp))
      {
        OPENSSL_cleanse(ab, kMPT_SCALAR_SIZE);
        OPENSSL_cleanse(abux, kMPT_SCALAR_SIZE);
        goto cleanup;
      }
    }
    OPENSSL_cleanse(ab, kMPT_SCALAR_SIZE);
    OPENSSL_cleanse(abux, kMPT_SCALAR_SIZE);
  }

  if (!RHS_inited)
    goto cleanup;
  ok = pubkey_equal(ctx, &P, &RHS) ? 1 : 0;

cleanup:
  OPENSSL_cleanse(x, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(x_inv, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(last, kMPT_SCALAR_SIZE);
  if (Gw)
    OPENSSL_cleanse(Gw, capacity * sizeof(secp256k1_pubkey));
  if (Hw)
    OPENSSL_cleanse(Hw, capacity * sizeof(secp256k1_pubkey));
  free(Gw);
  free(Hw);
  return ok;
}

/* ==========================================================================
 * Pure 3-way IPA with early termination.
 *
 * Recursion is identical to the baseline pure-3W implementation, except that
 * it stops as soon as the current vector length is <= 3.  The prover then
 * reveals the remaining a/b vectors (1, 2, or 3 scalars each) instead of
 * executing one more 3W round.
 *
 * This is intentionally an IPA-only experimental path.  It does not replace
 * the serialized aggregated Bulletproof format yet.
 * ========================================================================== */

static inline size_t bp_ipa_rounds_3w_et(size_t n)
{
  size_t r = 0;
  while (n > 3)
  {
    n = (n + 2) / 3; /* ceil(n/3) */
    r++;
  }
  return r;
}

static inline size_t bp_ipa_terminal_len_3w_et(size_t n)
{
  while (n > 3)
    n = (n + 2) / 3;
  return n;
}

/*
 * 3W prover with early termination at current dimension <= 3.
 *
 * a_terminal and b_terminal each provide space for exactly 3 scalars.
 * Unused slots are zeroed.  terminal_n_out is optional and is derivable from n.
 */
int secp256k1_bulletproof_run_ipa_prover_3w_et(
    const secp256k1_context *ctx, const secp256k1_pubkey *U,
    const secp256k1_pubkey *G_vec, const secp256k1_pubkey *H_vec,
    const unsigned char *a_vec, const unsigned char *b_vec, size_t n,
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE],
    const unsigned char ux_scalar[kMPT_SCALAR_SIZE],
    secp256k1_pubkey *L1_out, secp256k1_pubkey *L2_out,
    secp256k1_pubkey *R1_out, secp256k1_pubkey *R2_out, size_t max_rounds,
    size_t *rounds_out,
    unsigned char a_terminal[3 * kMPT_SCALAR_SIZE],
    unsigned char b_terminal[3 * kMPT_SCALAR_SIZE],
    size_t *terminal_n_out)
{
  const size_t rounds = bp_ipa_rounds_3w_et(n);
  const size_t capacity = n + 2;
  secp256k1_pubkey *Gw = NULL, *Hw = NULL;
  unsigned char *aw = NULL, *bw = NULL;
  unsigned char x[kMPT_SCALAR_SIZE] = {0};
  unsigned char x_inv[kMPT_SCALAR_SIZE] = {0};
  unsigned char last[kMPT_SCALAR_SIZE] = {0};
  size_t cur_n = n;
  int ok = 0;

  if (!ctx || !U || !G_vec || !H_vec || !a_vec || !b_vec ||
      !a_terminal || !b_terminal || n == 0 || rounds > max_rounds)
    return 0;

  if (rounds > 0 &&
      (!L1_out || !L2_out || !R1_out || !R2_out))
    return 0;

  Gw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  Hw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  aw = (unsigned char *)malloc(capacity * kMPT_SCALAR_SIZE);
  bw = (unsigned char *)malloc(capacity * kMPT_SCALAR_SIZE);
  if (!Gw || !Hw || !aw || !bw)
    goto cleanup;

  memcpy(Gw, G_vec, n * sizeof(secp256k1_pubkey));
  memcpy(Hw, H_vec, n * sizeof(secp256k1_pubkey));
  memcpy(aw, a_vec, n * kMPT_SCALAR_SIZE);
  memcpy(bw, b_vec, n * kMPT_SCALAR_SIZE);
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);

  for (size_t r = 0; r < rounds; r++)
  {
    const size_t padded_n = bp_ipa_padded_len_3w(cur_n);
    const size_t pad = padded_n - cur_n;
    const size_t third_n = padded_n / 3;

    if (cur_n <= 3 || padded_n > capacity)
      goto cleanup;

    if (pad)
    {
      memset(aw + cur_n * kMPT_SCALAR_SIZE, 0,
             pad * kMPT_SCALAR_SIZE);
      memset(bw + cur_n * kMPT_SCALAR_SIZE, 0,
             pad * kMPT_SCALAR_SIZE);

      if (!derive_ipa_pad_generators_3w(
              ctx, Gw + cur_n, Hw + cur_n, pad, n, r))
        goto cleanup;
    }

    if (!secp256k1_bulletproof_ipa_compute_LR_3w(
            ctx, &L1_out[r], &L2_out[r], &R1_out[r], &R2_out[r],
            aw, bw, Gw, Hw, U, ux_scalar, third_n))
      goto cleanup;

    if (!derive_ipa_round_challenge_3w(
            ctx, x, last, &L1_out[r], &L2_out[r],
            &R1_out[r], &R2_out[r]))
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    if (!secp256k1_bulletproof_ipa_compress_step_3w(
            ctx, aw, bw, Gw, Hw, third_n, x, x_inv))
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
    cur_n = third_n;
  }

  if (cur_n == 0 || cur_n > 3)
    goto cleanup;

  memset(a_terminal, 0, 3 * kMPT_SCALAR_SIZE);
  memset(b_terminal, 0, 3 * kMPT_SCALAR_SIZE);
  memcpy(a_terminal, aw, cur_n * kMPT_SCALAR_SIZE);
  memcpy(b_terminal, bw, cur_n * kMPT_SCALAR_SIZE);

  if (rounds_out)
    *rounds_out = rounds;
  if (terminal_n_out)
    *terminal_n_out = cur_n;

  ok = 1;

cleanup:
  OPENSSL_cleanse(x, sizeof(x));
  OPENSSL_cleanse(x_inv, sizeof(x_inv));
  OPENSSL_cleanse(last, sizeof(last));

  if (aw)
    OPENSSL_cleanse(aw, capacity * kMPT_SCALAR_SIZE);
  if (bw)
    OPENSSL_cleanse(bw, capacity * kMPT_SCALAR_SIZE);
  if (Gw)
    OPENSSL_cleanse(Gw, capacity * sizeof(secp256k1_pubkey));
  if (Hw)
    OPENSSL_cleanse(Hw, capacity * sizeof(secp256k1_pubkey));

  free(aw);
  free(bw);
  free(Gw);
  free(Hw);
  return ok;
}

/*
 * Explicit verifier for the early-termination 3W IPA.
 *
 * After applying all transmitted 3W rounds, the verifier has a terminal
 * statement of dimension t in {1,2,3}:
 *
 *   P_t = <a_t,G_t> + <b_t,H_t> + ux*<a_t,b_t>*U.
 *
 * It checks that relation directly.
 */
int ipa_verify_explicit_3w_et(
    const secp256k1_context *ctx, const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec, const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in, const secp256k1_pubkey *L1_vec,
    const secp256k1_pubkey *L2_vec, const secp256k1_pubkey *R1_vec,
    const secp256k1_pubkey *R2_vec, size_t n,
    const unsigned char a_terminal[3 * kMPT_SCALAR_SIZE],
    const unsigned char b_terminal[3 * kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  const size_t rounds = bp_ipa_rounds_3w_et(n);
  const size_t expected_terminal_n = bp_ipa_terminal_len_3w_et(n);
  const size_t capacity = n + 2;

  secp256k1_pubkey *Gw = NULL, *Hw = NULL;
  secp256k1_pubkey P, RHS;
  unsigned char x[kMPT_SCALAR_SIZE] = {0};
  unsigned char x_inv[kMPT_SCALAR_SIZE] = {0};
  unsigned char last[kMPT_SCALAR_SIZE] = {0};
  unsigned char dot[kMPT_SCALAR_SIZE] = {0};
  size_t cur_n = n;
  int RHS_inited = 0;
  int ok = 0;

  if (!ctx || !G_vec || !H_vec || !U || !P_in ||
      !a_terminal || !b_terminal || !ux || !ipa_transcript_id || n == 0)
    return 0;

  if (rounds > 0 &&
      (!L1_vec || !L2_vec || !R1_vec || !R2_vec))
    return 0;

  /* Terminal scalars must be canonical.  Unused fixed slots must be zero. */
  for (size_t i = 0; i < expected_terminal_n; i++)
  {
    if (!scalar_is_canonical_3w(
            a_terminal + i * kMPT_SCALAR_SIZE) ||
        !scalar_is_canonical_3w(
            b_terminal + i * kMPT_SCALAR_SIZE))
      return 0;
  }
  for (size_t i = expected_terminal_n; i < 3; i++)
  {
    if (!scalar_is_zero(a_terminal + i * kMPT_SCALAR_SIZE) ||
        !scalar_is_zero(b_terminal + i * kMPT_SCALAR_SIZE))
      return 0;
  }

  Gw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  Hw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  if (!Gw || !Hw)
    goto cleanup;

  memcpy(Gw, G_vec, n * sizeof(secp256k1_pubkey));
  memcpy(Hw, H_vec, n * sizeof(secp256k1_pubkey));
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);
  P = *P_in;

  for (size_t r = 0; r < rounds; r++)
  {
    const size_t padded_n = bp_ipa_padded_len_3w(cur_n);
    const size_t pad = padded_n - cur_n;
    const size_t third_n = padded_n / 3;

    if (cur_n <= 3 || padded_n > capacity)
      goto cleanup;

    if (!derive_ipa_round_challenge_3w(
            ctx, x, last, &L1_vec[r], &L2_vec[r],
            &R1_vec[r], &R2_vec[r]))
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    if (!apply_ipa_folding_to_P_3w(
            ctx, &P, &L1_vec[r], &L2_vec[r],
            &R1_vec[r], &R2_vec[r], x, x_inv))
      goto cleanup;

    if (pad &&
        !derive_ipa_pad_generators_3w(
            ctx, Gw + cur_n, Hw + cur_n, pad, n, r))
      goto cleanup;

    if (!fold_generators_step_3w(
            ctx, Gw, Hw, third_n, x, x_inv))
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
    cur_n = third_n;
  }

  if (cur_n != expected_terminal_n || cur_n == 0 || cur_n > 3)
    goto cleanup;

  if (!msm_add_checked_3w(
          ctx, &RHS, &RHS_inited, Gw, a_terminal, cur_n))
    goto cleanup;

  if (!msm_add_checked_3w(
          ctx, &RHS, &RHS_inited, Hw, b_terminal, cur_n))
    goto cleanup;

  if (!secp256k1_bulletproof_ipa_dot(
          ctx, dot, a_terminal, b_terminal, cur_n))
    goto cleanup;

  if (!add_scaled_U_term_3w(
          ctx, &RHS, &RHS_inited, U, dot, ux))
    goto cleanup;

  if (!RHS_inited)
    goto cleanup;

  ok = pubkey_equal(ctx, &P, &RHS) ? 1 : 0;

cleanup:
  OPENSSL_cleanse(x, sizeof(x));
  OPENSSL_cleanse(x_inv, sizeof(x_inv));
  OPENSSL_cleanse(last, sizeof(last));
  OPENSSL_cleanse(dot, sizeof(dot));

  if (Gw)
    OPENSSL_cleanse(Gw, capacity * sizeof(secp256k1_pubkey));
  if (Hw)
    OPENSSL_cleanse(Hw, capacity * sizeof(secp256k1_pubkey));

  free(Gw);
  free(Hw);
  return ok;
}

/* ==========================================================================
 * Optimized 3-way IPA verifiers (pure 3W and 3W + early termination).
 *
 * These functions verify exactly the same proofs as the explicit 3W verifiers.
 * The protocol, padding rule, Fiat-Shamir transcript, and proof bytes are
 * unchanged.  Only the verifier's generator reconstruction is optimized.
 *
 * Instead of physically folding all G/H generators round-by-round, we:
 *
 *   1. re-derive all 3W challenges x_r;
 *   2. determine the final coefficient and terminal slot of every original
 *      generator and every dynamically introduced padding generator;
 *   3. multiply those folding coefficients by the appropriate terminal
 *      a_j / b_j scalar;
 *   4. evaluate the complete G side with one MSM and the complete H side with
 *      one MSM;
 *   5. apply the ordinary P-side L1/L2/R1/R2 updates and compare.
 *
 * For one 3W round:
 *
 *   G' = x^{-1} G1 + G2 + x G3
 *   H' = x H1      + H2 + x^{-1} H3
 *
 * Hence a leaf in block 0/1/2 receives:
 *
 *   G factor: x^{-1}, 1, x
 *   H factor: x,      1, x^{-1}
 *
 * A dynamic pad generator begins participating only in the round in which it
 * is introduced.
 * ========================================================================== */

static void ipa3w_leaf_coefficients_and_slot(
    unsigned char g_coeff[kMPT_SCALAR_SIZE],
    unsigned char h_coeff[kMPT_SCALAR_SIZE],
    size_t *terminal_slot_out,
    size_t start_index,
    size_t start_round,
    const size_t *dims,
    const unsigned char *x_flat,
    const unsigned char *xinv_flat,
    size_t rounds)
{
  size_t idx = start_index;

  memset(g_coeff, 0, kMPT_SCALAR_SIZE);
  memset(h_coeff, 0, kMPT_SCALAR_SIZE);
  g_coeff[kMPT_SCALAR_SIZE - 1] = 1;
  h_coeff[kMPT_SCALAR_SIZE - 1] = 1;

  for (size_t r = start_round; r < rounds; ++r)
  {
    const size_t third_n = (dims[r] + 2) / 3;
    const size_t block = idx / third_n;
    const unsigned char *x = x_flat + r * kMPT_SCALAR_SIZE;
    const unsigned char *x_inv = xinv_flat + r * kMPT_SCALAR_SIZE;

    if (block == 0)
    {
      secp256k1_mpt_scalar_mul(g_coeff, g_coeff, x_inv);
      secp256k1_mpt_scalar_mul(h_coeff, h_coeff, x);
    }
    else if (block == 1)
    {
      /* Middle block has coefficient 1 for both G and H. */
    }
    else if (block == 2)
    {
      secp256k1_mpt_scalar_mul(g_coeff, g_coeff, x);
      secp256k1_mpt_scalar_mul(h_coeff, h_coeff, x_inv);
    }
    else
    {
      /*
       * This should be unreachable for a correctly padded 3W dimension.
       * Mark the output slot invalid so the caller rejects the proof.
       */
      *terminal_slot_out = (size_t)-1;
      return;
    }

    idx %= third_n;
  }

  *terminal_slot_out = idx;
}

static int ipa_verify_explicit_3w_fast_core(
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
    size_t rounds,
    size_t expected_terminal_n,
    const unsigned char a_terminal[3 * kMPT_SCALAR_SIZE],
    const unsigned char b_terminal[3 * kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  unsigned char *x_flat = NULL;
  unsigned char *xinv_flat = NULL;
  size_t *dims = NULL;

  secp256k1_pubkey *G_points = NULL;
  secp256k1_pubkey *H_points = NULL;
  unsigned char *G_scalars = NULL;
  unsigned char *H_scalars = NULL;

  secp256k1_pubkey P, RHS;
  unsigned char last[kMPT_SCALAR_SIZE] = {0};
  unsigned char dot[kMPT_SCALAR_SIZE] = {0};

  size_t pad_count = 0;
  size_t total_points = 0;
  int RHS_inited = 0;
  int ok = 0;

  if (!ctx || !G_vec || !H_vec || !U || !P_in ||
      !a_terminal || !b_terminal || !ux || !ipa_transcript_id ||
      n == 0 || expected_terminal_n == 0 || expected_terminal_n > 3)
    return 0;

  if (rounds > 0 &&
      (!L1_vec || !L2_vec || !R1_vec || !R2_vec))
    return 0;

  /* Match the slow ET verifier's canonicality and fixed-slot checks. */
  for (size_t i = 0; i < expected_terminal_n; ++i)
  {
    if (!scalar_is_canonical_3w(
            a_terminal + i * kMPT_SCALAR_SIZE) ||
        !scalar_is_canonical_3w(
            b_terminal + i * kMPT_SCALAR_SIZE))
      return 0;
  }

  for (size_t i = expected_terminal_n; i < 3; ++i)
  {
    if (!scalar_is_zero(a_terminal + i * kMPT_SCALAR_SIZE) ||
        !scalar_is_zero(b_terminal + i * kMPT_SCALAR_SIZE))
      return 0;
  }

  if (rounds > 0)
  {
    x_flat =
        (unsigned char *)malloc(rounds * kMPT_SCALAR_SIZE);
    xinv_flat =
        (unsigned char *)malloc(rounds * kMPT_SCALAR_SIZE);
    dims = (size_t *)malloc(rounds * sizeof(size_t));

    if (!x_flat || !xinv_flat || !dims)
      goto cleanup;
  }

  /*
   * Record the logical dimension entering every round and count the number of
   * independently derived pad-generator pairs.
   */
  {
    size_t cur_n = n;

    for (size_t r = 0; r < rounds; ++r)
    {
      const size_t padded_n = bp_ipa_padded_len_3w(cur_n);
      const size_t pad = padded_n - cur_n;

      dims[r] = cur_n;
      pad_count += pad;
      cur_n = padded_n / 3;
    }

    if (cur_n != expected_terminal_n)
      goto cleanup;
  }

  /*
   * Re-derive the transcript challenges and update P exactly as the baseline
   * verifier does.  The P-side work is only four public point scalings per
   * round, so the optimization targets the much larger G/H recursion.
   */
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);
  P = *P_in;

  for (size_t r = 0; r < rounds; ++r)
  {
    unsigned char *x = x_flat + r * kMPT_SCALAR_SIZE;
    unsigned char *x_inv = xinv_flat + r * kMPT_SCALAR_SIZE;

    if (!derive_ipa_round_challenge_3w(
            ctx, x, last, &L1_vec[r], &L2_vec[r],
            &R1_vec[r], &R2_vec[r]))
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    if (!apply_ipa_folding_to_P_3w(
            ctx, &P, &L1_vec[r], &L2_vec[r],
            &R1_vec[r], &R2_vec[r], x, x_inv))
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
  }

  total_points = n + pad_count;

  G_points =
      (secp256k1_pubkey *)malloc(total_points * sizeof(secp256k1_pubkey));
  H_points =
      (secp256k1_pubkey *)malloc(total_points * sizeof(secp256k1_pubkey));
  G_scalars =
      (unsigned char *)malloc(total_points * kMPT_SCALAR_SIZE);
  H_scalars =
      (unsigned char *)malloc(total_points * kMPT_SCALAR_SIZE);

  if (!G_points || !H_points || !G_scalars || !H_scalars)
    goto cleanup;

  /*
   * Original leaves.
   *
   * We directly compute each leaf's contribution to the final terminal
   * relation.  If a leaf ends in terminal slot j:
   *
   *   G scalar = folding_coefficient_G * a_terminal[j]
   *   H scalar = folding_coefficient_H * b_terminal[j]
   *
   * This lets us evaluate all terminal G vectors with one MSM and all terminal
   * H vectors with one MSM, even when ET stops at dimension 2 or 3.
   */
  for (size_t i = 0; i < n; ++i)
  {
    unsigned char g_fold[kMPT_SCALAR_SIZE];
    unsigned char h_fold[kMPT_SCALAR_SIZE];
    size_t slot = 0;

    G_points[i] = G_vec[i];
    H_points[i] = H_vec[i];

    ipa3w_leaf_coefficients_and_slot(
        g_fold, h_fold, &slot,
        i, 0, dims, x_flat, xinv_flat, rounds);

    if (slot >= expected_terminal_n)
    {
      OPENSSL_cleanse(g_fold, sizeof(g_fold));
      OPENSSL_cleanse(h_fold, sizeof(h_fold));
      goto cleanup;
    }

    secp256k1_mpt_scalar_mul(
        G_scalars + i * kMPT_SCALAR_SIZE,
        g_fold,
        a_terminal + slot * kMPT_SCALAR_SIZE);

    secp256k1_mpt_scalar_mul(
        H_scalars + i * kMPT_SCALAR_SIZE,
        h_fold,
        b_terminal + slot * kMPT_SCALAR_SIZE);

    OPENSSL_cleanse(g_fold, sizeof(g_fold));
    OPENSSL_cleanse(h_fold, sizeof(h_fold));
  }

  /*
   * Dynamic padding leaves.
   *
   * At round r, padding points occupy indices dims[r], dims[r]+1 (as needed)
   * in the freshly padded vector.  They begin accumulating fold factors at
   * round r and do not participate in any prior challenge.
   */
  {
    size_t out = n;

    for (size_t r = 0; r < rounds; ++r)
    {
      const size_t padded_n = bp_ipa_padded_len_3w(dims[r]);
      const size_t pad = padded_n - dims[r];

      if (pad == 0)
        continue;

      if (!derive_ipa_pad_generators_3w(
              ctx, G_points + out, H_points + out,
              pad, n, r))
        goto cleanup;

      for (size_t k = 0; k < pad; ++k)
      {
        unsigned char g_fold[kMPT_SCALAR_SIZE];
        unsigned char h_fold[kMPT_SCALAR_SIZE];
        size_t slot = 0;

        ipa3w_leaf_coefficients_and_slot(
            g_fold, h_fold, &slot,
            dims[r] + k, r,
            dims, x_flat, xinv_flat, rounds);

        if (slot >= expected_terminal_n)
        {
          OPENSSL_cleanse(g_fold, sizeof(g_fold));
          OPENSSL_cleanse(h_fold, sizeof(h_fold));
          goto cleanup;
        }

        secp256k1_mpt_scalar_mul(
            G_scalars + out * kMPT_SCALAR_SIZE,
            g_fold,
            a_terminal + slot * kMPT_SCALAR_SIZE);

        secp256k1_mpt_scalar_mul(
            H_scalars + out * kMPT_SCALAR_SIZE,
            h_fold,
            b_terminal + slot * kMPT_SCALAR_SIZE);

        OPENSSL_cleanse(g_fold, sizeof(g_fold));
        OPENSSL_cleanse(h_fold, sizeof(h_fold));
        ++out;
      }
    }

    if (out != total_points)
      goto cleanup;
  }

  /* Complete G and H sides with one MSM each. */
  if (!msm_try_add(
          ctx, &RHS, &RHS_inited,
          G_points, G_scalars, total_points))
    goto cleanup;

  if (!msm_try_add(
          ctx, &RHS, &RHS_inited,
          H_points, H_scalars, total_points))
    goto cleanup;

  /* Add ux * <a_terminal,b_terminal> * U. */
  if (!secp256k1_bulletproof_ipa_dot(
          ctx, dot, a_terminal, b_terminal, expected_terminal_n))
    goto cleanup;

  if (!add_scaled_U_term_3w(
          ctx, &RHS, &RHS_inited, U, dot, ux))
    goto cleanup;

  if (!RHS_inited)
    goto cleanup;

  ok = pubkey_equal(ctx, &P, &RHS) ? 1 : 0;

cleanup:
  OPENSSL_cleanse(last, sizeof(last));
  OPENSSL_cleanse(dot, sizeof(dot));

  if (x_flat)
    OPENSSL_cleanse(x_flat, rounds * kMPT_SCALAR_SIZE);
  if (xinv_flat)
    OPENSSL_cleanse(xinv_flat, rounds * kMPT_SCALAR_SIZE);
  if (dims)
    OPENSSL_cleanse(dims, rounds * sizeof(size_t));
  if (G_scalars)
    OPENSSL_cleanse(G_scalars, total_points * kMPT_SCALAR_SIZE);
  if (H_scalars)
    OPENSSL_cleanse(H_scalars, total_points * kMPT_SCALAR_SIZE);
  if (G_points)
    OPENSSL_cleanse(
        G_points, total_points * sizeof(secp256k1_pubkey));
  if (H_points)
    OPENSSL_cleanse(
        H_points, total_points * sizeof(secp256k1_pubkey));

  free(x_flat);
  free(xinv_flat);
  free(dims);
  free(G_points);
  free(H_points);
  free(G_scalars);
  free(H_scalars);

  return ok;
}

/* Optimized verifier for the ordinary pure-3W proof (terminal dimension 1). */
int ipa_verify_explicit_3w_fast(
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
    const unsigned char a_final[kMPT_SCALAR_SIZE],
    const unsigned char b_final[kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  unsigned char a_terminal[3 * kMPT_SCALAR_SIZE] = {0};
  unsigned char b_terminal[3 * kMPT_SCALAR_SIZE] = {0};

  if (!a_final || !b_final)
    return 0;

  memcpy(a_terminal, a_final, kMPT_SCALAR_SIZE);
  memcpy(b_terminal, b_final, kMPT_SCALAR_SIZE);

  return ipa_verify_explicit_3w_fast_core(
      ctx, G_vec, H_vec, U, P_in,
      L1_vec, L2_vec, R1_vec, R2_vec,
      n, bp_ipa_rounds_3w(n), 1,
      a_terminal, b_terminal, ux, ipa_transcript_id);
}

/* Optimized verifier for 3W with early termination at dimension <= 3. */
int ipa_verify_explicit_3w_et_fast(
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
    const unsigned char a_terminal[3 * kMPT_SCALAR_SIZE],
    const unsigned char b_terminal[3 * kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  return ipa_verify_explicit_3w_fast_core(
      ctx, G_vec, H_vec, U, P_in,
      L1_vec, L2_vec, R1_vec, R2_vec,
      n,
      bp_ipa_rounds_3w_et(n),
      bp_ipa_terminal_len_3w_et(n),
      a_terminal, b_terminal,
      ux, ipa_transcript_id);
}

/* ==========================================================================
 * Dynamically padded 2-way IPA.
 *
 * This is the binary analogue of the dynamic-padding policy used by the 3W
 * implementation.  At each recursion level:
 *
 *   - if cur_n is even, split directly into two equal halves;
 *   - if cur_n is odd, append exactly one zero coordinate and one
 *     deterministically derived G/H generator pair, then split.
 *
 * Thus the next dimension is always ceil(cur_n / 2), rather than globally
 * padding the original problem to the next power of two.
 *
 * The final dimension is 1.  This experimental path is IPA-only and does not
 * replace the existing serialized Bulletproof format.
 * ========================================================================== */

static inline size_t bp_ipa_rounds_2w_dynamic(size_t n)
{
  size_t r = 0;
  while (n > 1)
  {
    n = (n + 1) / 2; /* ceil(n/2) */
    ++r;
  }
  return r;
}

static inline size_t bp_ipa_padded_len_2w(size_t n)
{
  return n + (n & 1u);
}

static void ipa2w_store_u64_be(unsigned char out[8], uint64_t x)
{
  for (int i = 7; i >= 0; --i)
  {
    out[i] = (unsigned char)(x & 0xffu);
    x >>= 8;
  }
}

/*
 * Derive the single padding G/H coordinate used by an odd 2W round.
 *
 * Domain separation includes:
 *   - protocol/role tag,
 *   - original logical n,
 *   - recursion round.
 *
 * Prover and verifier call this function with identical inputs.
 */
static int derive_ipa_pad_generators_2w(
    const secp256k1_context *ctx,
    secp256k1_pubkey *G_pad,
    secp256k1_pubkey *H_pad,
    size_t original_n,
    size_t round)
{
  unsigned char label_g[32] = {0};
  unsigned char label_h[32] = {0};

  static const unsigned char tag_g[] = "IPA2W_DYN_PAD_G";
  static const unsigned char tag_h[] = "IPA2W_DYN_PAD_H";

  memcpy(label_g, tag_g, sizeof(tag_g) - 1);
  memcpy(label_h, tag_h, sizeof(tag_h) - 1);

  ipa2w_store_u64_be(label_g + 16, (uint64_t)original_n);
  ipa2w_store_u64_be(label_h + 16, (uint64_t)original_n);
  ipa2w_store_u64_be(label_g + 24, (uint64_t)round);
  ipa2w_store_u64_be(label_h + 24, (uint64_t)round);

  if (!secp256k1_mpt_get_generator_vector(ctx, G_pad, 1, label_g, sizeof(label_g)))
    return 0;
  if (!secp256k1_mpt_get_generator_vector(ctx, H_pad, 1, label_h, sizeof(label_h)))
    return 0;

  return 1;
}

/* Apply one standard binary IPA verifier update:
 *
 *   P <- P + x^2 L + x^{-2} R
 */
static int apply_ipa_folding_to_P_2w_one(
    const secp256k1_context *ctx,
    secp256k1_pubkey *P,
    const secp256k1_pubkey *L,
    const secp256k1_pubkey *R,
    const unsigned char x[kMPT_SCALAR_SIZE],
    const unsigned char x_inv[kMPT_SCALAR_SIZE])
{
  unsigned char x_sq[kMPT_SCALAR_SIZE];
  unsigned char xinv_sq[kMPT_SCALAR_SIZE];
  secp256k1_pubkey tL = *L, tR = *R, newP;
  const secp256k1_pubkey *pts[3];

  secp256k1_mpt_scalar_mul(x_sq, x, x);
  secp256k1_mpt_scalar_mul(xinv_sq, x_inv, x_inv);

  if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tL, x_sq))
    goto fail;
  if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tR, xinv_sq))
    goto fail;

  pts[0] = P;
  pts[1] = &tL;
  pts[2] = &tR;
  if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts, 3))
    goto fail;

  *P = newP;
  OPENSSL_cleanse(x_sq, sizeof(x_sq));
  OPENSSL_cleanse(xinv_sq, sizeof(xinv_sq));
  return 1;

fail:
  OPENSSL_cleanse(x_sq, sizeof(x_sq));
  OPENSSL_cleanse(xinv_sq, sizeof(xinv_sq));
  return 0;
}

/* Fold only G/H for a binary verifier round.
 *
 *   G'[i] = G_L[i] * x^{-1} + G_R[i] * x
 *   H'[i] = H_L[i] * x      + H_R[i] * x^{-1}
 */
static int fold_generators_step_2w(
    const secp256k1_context *ctx,
    secp256k1_pubkey *G,
    secp256k1_pubkey *H,
    size_t half_n,
    const unsigned char x[kMPT_SCALAR_SIZE],
    const unsigned char x_inv[kMPT_SCALAR_SIZE])
{
  for (size_t i = 0; i < half_n; ++i)
  {
    secp256k1_pubkey left, right;
    const secp256k1_pubkey *pts[2];

    left = G[i];
    right = G[i + half_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &left, x_inv))
      return 0;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &right, x))
      return 0;
    pts[0] = &left;
    pts[1] = &right;
    if (!secp256k1_ec_pubkey_combine(ctx, &G[i], pts, 2))
      return 0;

    left = H[i];
    right = H[i + half_n];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &left, x))
      return 0;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &right, x_inv))
      return 0;
    pts[0] = &left;
    pts[1] = &right;
    if (!secp256k1_ec_pubkey_combine(ctx, &H[i], pts, 2))
      return 0;
  }

  return 1;
}

/*
 * Binary IPA prover with local/dynamic padding.
 *
 * Unlike secp256k1_bulletproof_run_ipa_prover(), this function accepts any
 * logical n >= 1 and does not mutate caller-owned vectors.
 */
int secp256k1_bulletproof_run_ipa_prover_2w_dynamic(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const unsigned char *a_vec,
    const unsigned char *b_vec,
    size_t n,
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE],
    const unsigned char ux_scalar[kMPT_SCALAR_SIZE],
    secp256k1_pubkey *L_out,
    secp256k1_pubkey *R_out,
    size_t max_rounds,
    size_t *rounds_out,
    unsigned char a_final[kMPT_SCALAR_SIZE],
    unsigned char b_final[kMPT_SCALAR_SIZE])
{
  const size_t rounds = bp_ipa_rounds_2w_dynamic(n);
  const size_t capacity = n + 1;

  secp256k1_pubkey *Gw = NULL, *Hw = NULL;
  unsigned char *aw = NULL, *bw = NULL;

  unsigned char x[kMPT_SCALAR_SIZE] = {0};
  unsigned char x_inv[kMPT_SCALAR_SIZE] = {0};
  unsigned char last[kMPT_SCALAR_SIZE] = {0};

  size_t cur_n = n;
  int ok = 0;

  if (!ctx || !U || !G_vec || !H_vec || !a_vec || !b_vec ||
      !ipa_transcript_id || !ux_scalar || !a_final || !b_final ||
      n == 0 || rounds > max_rounds)
    return 0;

  if (rounds > 0 && (!L_out || !R_out))
    return 0;

  Gw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  Hw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  aw = (unsigned char *)malloc(capacity * kMPT_SCALAR_SIZE);
  bw = (unsigned char *)malloc(capacity * kMPT_SCALAR_SIZE);

  if (!Gw || !Hw || !aw || !bw)
    goto cleanup;

  memcpy(Gw, G_vec, n * sizeof(secp256k1_pubkey));
  memcpy(Hw, H_vec, n * sizeof(secp256k1_pubkey));
  memcpy(aw, a_vec, n * kMPT_SCALAR_SIZE);
  memcpy(bw, b_vec, n * kMPT_SCALAR_SIZE);
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);

  for (size_t r = 0; r < rounds; ++r)
  {
    const size_t padded_n = bp_ipa_padded_len_2w(cur_n);
    const size_t half_n = padded_n / 2;

    if (cur_n <= 1 || padded_n > capacity)
      goto cleanup;

    if (padded_n != cur_n)
    {
      memset(aw + cur_n * kMPT_SCALAR_SIZE, 0, kMPT_SCALAR_SIZE);
      memset(bw + cur_n * kMPT_SCALAR_SIZE, 0, kMPT_SCALAR_SIZE);

      if (!derive_ipa_pad_generators_2w(
              ctx, &Gw[cur_n], &Hw[cur_n], n, r))
        goto cleanup;
    }

    if (!secp256k1_bulletproof_ipa_compute_LR(
            ctx, &L_out[r], &R_out[r],
            aw, aw + half_n * kMPT_SCALAR_SIZE,
            bw, bw + half_n * kMPT_SCALAR_SIZE,
            Gw, Gw + half_n,
            Hw, Hw + half_n,
            U, ux_scalar, half_n))
      goto cleanup;

    if (!derive_ipa_round_challenge(
            ctx, x, last, &L_out[r], &R_out[r]))
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    if (!secp256k1_bulletproof_ipa_compress_step(
            ctx, aw, bw, Gw, Hw, half_n, x, x_inv))
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
    cur_n = half_n;
  }

  if (cur_n != 1)
    goto cleanup;

  memcpy(a_final, aw, kMPT_SCALAR_SIZE);
  memcpy(b_final, bw, kMPT_SCALAR_SIZE);

  if (rounds_out)
    *rounds_out = rounds;

  ok = 1;

cleanup:
  OPENSSL_cleanse(x, sizeof(x));
  OPENSSL_cleanse(x_inv, sizeof(x_inv));
  OPENSSL_cleanse(last, sizeof(last));

  if (aw)
    OPENSSL_cleanse(aw, capacity * kMPT_SCALAR_SIZE);
  if (bw)
    OPENSSL_cleanse(bw, capacity * kMPT_SCALAR_SIZE);
  if (Gw)
    OPENSSL_cleanse(Gw, capacity * sizeof(secp256k1_pubkey));
  if (Hw)
    OPENSSL_cleanse(Hw, capacity * sizeof(secp256k1_pubkey));

  free(aw);
  free(bw);
  free(Gw);
  free(Hw);
  return ok;
}

/*
 * Explicit verifier for dynamically padded binary IPA.
 *
 * Generator folding is deliberately performed round-by-round so that the
 * implementation follows the same dynamic dimensions as the prover.
 */
int ipa_verify_explicit_2w_dynamic(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L_vec,
    const secp256k1_pubkey *R_vec,
    size_t n,
    const unsigned char a_final[kMPT_SCALAR_SIZE],
    const unsigned char b_final[kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  const size_t rounds = bp_ipa_rounds_2w_dynamic(n);
  const size_t capacity = n + 1;

  secp256k1_pubkey *Gw = NULL, *Hw = NULL;
  secp256k1_pubkey P, RHS, tmp;

  unsigned char x[kMPT_SCALAR_SIZE] = {0};
  unsigned char x_inv[kMPT_SCALAR_SIZE] = {0};
  unsigned char last[kMPT_SCALAR_SIZE] = {0};

  size_t cur_n = n;
  int RHS_inited = 0;
  int ok = 0;

  if (!ctx || !G_vec || !H_vec || !U || !P_in ||
      !a_final || !b_final || !ux || !ipa_transcript_id || n == 0)
    return 0;

  if (rounds > 0 && (!L_vec || !R_vec))
    return 0;

  if (!scalar_is_canonical_3w(a_final) ||
      !scalar_is_canonical_3w(b_final))
    return 0;

  Gw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  Hw = (secp256k1_pubkey *)malloc(capacity * sizeof(secp256k1_pubkey));
  if (!Gw || !Hw)
    goto cleanup;

  memcpy(Gw, G_vec, n * sizeof(secp256k1_pubkey));
  memcpy(Hw, H_vec, n * sizeof(secp256k1_pubkey));
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);
  P = *P_in;

  for (size_t r = 0; r < rounds; ++r)
  {
    const size_t padded_n = bp_ipa_padded_len_2w(cur_n);
    const size_t half_n = padded_n / 2;

    if (cur_n <= 1 || padded_n > capacity)
      goto cleanup;

    if (!derive_ipa_round_challenge(
            ctx, x, last, &L_vec[r], &R_vec[r]))
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    if (!apply_ipa_folding_to_P_2w_one(
            ctx, &P, &L_vec[r], &R_vec[r], x, x_inv))
      goto cleanup;

    if (padded_n != cur_n)
    {
      if (!derive_ipa_pad_generators_2w(
              ctx, &Gw[cur_n], &Hw[cur_n], n, r))
        goto cleanup;
    }

    if (!fold_generators_step_2w(
            ctx, Gw, Hw, half_n, x, x_inv))
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
    cur_n = half_n;
  }

  if (cur_n != 1)
    goto cleanup;

  /* RHS = a*Gf + b*Hf + (a*b*ux)*U */
  if (!scalar_is_zero(a_final))
  {
    tmp = Gw[0];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, a_final) ||
        !add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }

  if (!scalar_is_zero(b_final))
  {
    tmp = Hw[0];
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, b_final) ||
        !add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }

  {
    unsigned char ab[kMPT_SCALAR_SIZE];
    unsigned char abux[kMPT_SCALAR_SIZE];

    secp256k1_mpt_scalar_mul(ab, a_final, b_final);
    secp256k1_mpt_scalar_mul(abux, ab, ux);

    if (!scalar_is_zero(abux))
    {
      tmp = *U;
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, abux) ||
          !add_term(ctx, &RHS, &RHS_inited, &tmp))
      {
        OPENSSL_cleanse(ab, sizeof(ab));
        OPENSSL_cleanse(abux, sizeof(abux));
        goto cleanup;
      }
    }

    OPENSSL_cleanse(ab, sizeof(ab));
    OPENSSL_cleanse(abux, sizeof(abux));
  }

  if (!RHS_inited)
    goto cleanup;

  ok = pubkey_equal(ctx, &P, &RHS) ? 1 : 0;

cleanup:
  OPENSSL_cleanse(x, sizeof(x));
  OPENSSL_cleanse(x_inv, sizeof(x_inv));
  OPENSSL_cleanse(last, sizeof(last));

  if (Gw)
    OPENSSL_cleanse(Gw, capacity * sizeof(secp256k1_pubkey));
  if (Hw)
    OPENSSL_cleanse(Hw, capacity * sizeof(secp256k1_pubkey));

  free(Gw);
  free(Hw);
  return ok;
}

/* ==========================================================================
 * Optimized verifier for dynamically padded 2-way IPA.
 *
 * The baseline dynamic verifier explicitly folds every G/H point at every
 * recursion level.  This verifier instead:
 *
 *   1. re-derives all Fiat-Shamir challenges;
 *   2. computes, in the scalar field, the final coefficient of every original
 *      generator and every dynamically introduced padding generator;
 *   3. evaluates G_f and H_f with one MSM each;
 *   4. applies the usual L/R updates to P and performs the final IPA check.
 *
 * For an exact power-of-two input no dynamic padding occurs, so the proof is
 * byte-for-byte the standard binary IPA proof.  In that case we deliberately
 * dispatch to ipa_verify_explicit(), giving the optimized standard verifier as
 * the exact fast path and making the power-of-two control comparison clean.
 * ========================================================================== */

static inline int bp_is_power_of_two_2w_fast(size_t n)
{
  return n != 0 && (n & (n - 1)) == 0;
}

/*
 * Compute the coefficient with which one leaf generator contributes to the
 * final folded generator.
 *
 * A leaf may be:
 *   - an original generator, born at round 0 with index i, or
 *   - a dynamic pad generator, born at an odd round r at index cur_n[r].
 *
 * G folding:
 *   left  -> x^{-1}
 *   right -> x
 *
 * H folding:
 *   left  -> x
 *   right -> x^{-1}
 */
static void ipa2w_dynamic_leaf_coefficients(
    unsigned char g_coeff[kMPT_SCALAR_SIZE],
    unsigned char h_coeff[kMPT_SCALAR_SIZE],
    size_t start_index,
    size_t start_round,
    const size_t *dims,
    const unsigned char *u_flat,
    const unsigned char *uinv_flat,
    size_t rounds)
{
  size_t idx = start_index;

  memset(g_coeff, 0, kMPT_SCALAR_SIZE);
  memset(h_coeff, 0, kMPT_SCALAR_SIZE);
  g_coeff[kMPT_SCALAR_SIZE - 1] = 1;
  h_coeff[kMPT_SCALAR_SIZE - 1] = 1;

  for (size_t r = start_round; r < rounds; ++r)
  {
    const size_t half_n = (dims[r] + 1) / 2;
    const int is_right = idx >= half_n;

    const unsigned char *x =
        u_flat + r * kMPT_SCALAR_SIZE;
    const unsigned char *x_inv =
        uinv_flat + r * kMPT_SCALAR_SIZE;

    if (!is_right)
    {
      secp256k1_mpt_scalar_mul(g_coeff, g_coeff, x_inv);
      secp256k1_mpt_scalar_mul(h_coeff, h_coeff, x);
    }
    else
    {
      secp256k1_mpt_scalar_mul(g_coeff, g_coeff, x);
      secp256k1_mpt_scalar_mul(h_coeff, h_coeff, x_inv);
      idx -= half_n;
    }
  }
}

int ipa_verify_explicit(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L_vec,
    const secp256k1_pubkey *R_vec,
    size_t n,
    const unsigned char a_final[kMPT_SCALAR_SIZE],
    const unsigned char b_final[kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE]);


/*
 * Optimized explicit verifier for binary IPA with local/dynamic padding.
 *
 * The accepted proof format is identical to ipa_verify_explicit_2w_dynamic().
 * Only the verifier implementation changes.
 */
int ipa_verify_explicit_2w_dynamic_fast(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec,
    const secp256k1_pubkey *H_vec,
    const secp256k1_pubkey *U,
    const secp256k1_pubkey *P_in,
    const secp256k1_pubkey *L_vec,
    const secp256k1_pubkey *R_vec,
    size_t n,
    const unsigned char a_final[kMPT_SCALAR_SIZE],
    const unsigned char b_final[kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  const size_t rounds = bp_ipa_rounds_2w_dynamic(n);

  unsigned char *u_flat = NULL;
  unsigned char *uinv_flat = NULL;
  size_t *dims = NULL;

  secp256k1_pubkey *G_points = NULL;
  secp256k1_pubkey *H_points = NULL;
  unsigned char *G_scalars = NULL;
  unsigned char *H_scalars = NULL;

  secp256k1_pubkey P, Gf, Hf, RHS, tmp;
  int RHS_inited = 0;
  int ok = 0;

  unsigned char last[kMPT_SCALAR_SIZE] = {0};
  size_t pad_count = 0;
  size_t total_points = 0;

  if (!ctx || !G_vec || !H_vec || !U || !P_in ||
      !a_final || !b_final || !ux || !ipa_transcript_id || n == 0)
    return 0;

  if (rounds > 0 && (!L_vec || !R_vec))
    return 0;

  if (!scalar_is_canonical_3w(a_final) ||
      !scalar_is_canonical_3w(b_final))
    return 0;

  /*
   * At powers of two the dynamic prover performs no padding at any level and
   * therefore generates the ordinary binary IPA proof.  Reuse the existing
   * optimized verifier exactly.
   */
  if (n > 1 && bp_is_power_of_two_2w_fast(n))
  {
    return ipa_verify_explicit(
        ctx, G_vec, H_vec, U, P_in, L_vec, R_vec, n,
        a_final, b_final, ux, ipa_transcript_id);
  }

  if (rounds > 0)
  {
    u_flat =
        (unsigned char *)malloc(rounds * kMPT_SCALAR_SIZE);
    uinv_flat =
        (unsigned char *)malloc(rounds * kMPT_SCALAR_SIZE);
    dims = (size_t *)malloc(rounds * sizeof(size_t));

    if (!u_flat || !uinv_flat || !dims)
      goto cleanup;
  }

  /*
   * Record the logical dimension entering every round and count how many
   * independent pad-generator pairs are introduced.
   */
  {
    size_t cur_n = n;
    for (size_t r = 0; r < rounds; ++r)
    {
      dims[r] = cur_n;
      if (cur_n & 1u)
        ++pad_count;
      cur_n = (cur_n + 1) / 2;
    }

    if (cur_n != 1)
      goto cleanup;
  }

  /*
   * Re-derive all challenges exactly as the prover and the baseline verifier
   * do.  The transcript itself is unchanged by this optimization.
   */
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);

  for (size_t r = 0; r < rounds; ++r)
  {
    unsigned char *x =
        u_flat + r * kMPT_SCALAR_SIZE;
    unsigned char *x_inv =
        uinv_flat + r * kMPT_SCALAR_SIZE;

    if (!derive_ipa_round_challenge(
            ctx, x, last, &L_vec[r], &R_vec[r]))
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(x_inv, x) ||
        secp256k1_ec_seckey_verify(ctx, x_inv) != 1)
      goto cleanup;

    memcpy(last, x, kMPT_SCALAR_SIZE);
  }

  total_points = n + pad_count;

  G_points =
      (secp256k1_pubkey *)malloc(total_points * sizeof(secp256k1_pubkey));
  H_points =
      (secp256k1_pubkey *)malloc(total_points * sizeof(secp256k1_pubkey));
  G_scalars =
      (unsigned char *)malloc(total_points * kMPT_SCALAR_SIZE);
  H_scalars =
      (unsigned char *)malloc(total_points * kMPT_SCALAR_SIZE);

  if (!G_points || !H_points || !G_scalars || !H_scalars)
    goto cleanup;

  /*
   * Original generator leaves.
   *
   * Their indices start at the original IPA dimension and are followed through
   * the changing sequence
   *
   *   n -> ceil(n/2) -> ceil(n/4) -> ...
   *
   * using only scalar arithmetic.
   */
  for (size_t i = 0; i < n; ++i)
  {
    G_points[i] = G_vec[i];
    H_points[i] = H_vec[i];

    ipa2w_dynamic_leaf_coefficients(
        G_scalars + i * kMPT_SCALAR_SIZE,
        H_scalars + i * kMPT_SCALAR_SIZE,
        i, 0, dims, u_flat, uinv_flat, rounds);
  }

  /*
   * Padding leaves.
   *
   * If dims[r] is odd, the prover appends one new generator at index dims[r]
   * immediately before round r.  That leaf participates starting at r, not in
   * earlier rounds.
   */
  {
    size_t out = n;

    for (size_t r = 0; r < rounds; ++r)
    {
      if ((dims[r] & 1u) == 0)
        continue;

      if (!derive_ipa_pad_generators_2w(
              ctx, &G_points[out], &H_points[out], n, r))
        goto cleanup;

      ipa2w_dynamic_leaf_coefficients(
          G_scalars + out * kMPT_SCALAR_SIZE,
          H_scalars + out * kMPT_SCALAR_SIZE,
          dims[r], r, dims, u_flat, uinv_flat, rounds);

      ++out;
    }

    if (out != total_points)
      goto cleanup;
  }

  /*
   * Reconstruct the two final folded generators with one MSM each instead of
   * repeatedly folding all points at every recursion level.
   */
  if (!secp256k1_bulletproof_ipa_msm(
          ctx, &Gf, G_points, G_scalars, total_points))
    goto cleanup;

  if (!secp256k1_bulletproof_ipa_msm(
          ctx, &Hf, H_points, H_scalars, total_points))
    goto cleanup;

  /* RHS = a*Gf + b*Hf + (a*b*ux)*U */
  if (!scalar_is_zero(a_final))
  {
    tmp = Gf;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, a_final) ||
        !add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }

  if (!scalar_is_zero(b_final))
  {
    tmp = Hf;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, b_final) ||
        !add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }

  {
    unsigned char ab[kMPT_SCALAR_SIZE];
    unsigned char abux[kMPT_SCALAR_SIZE];

    secp256k1_mpt_scalar_mul(ab, a_final, b_final);
    secp256k1_mpt_scalar_mul(abux, ab, ux);

    if (!scalar_is_zero(abux))
    {
      tmp = *U;
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, abux) ||
          !add_term(ctx, &RHS, &RHS_inited, &tmp))
      {
        OPENSSL_cleanse(ab, sizeof(ab));
        OPENSSL_cleanse(abux, sizeof(abux));
        goto cleanup;
      }
    }

    OPENSSL_cleanse(ab, sizeof(ab));
    OPENSSL_cleanse(abux, sizeof(abux));
  }

  if (!RHS_inited)
    goto cleanup;

  /*
   * The P-side recursion is already cheap: two public point scalings per round.
   * Reuse the existing verifier helper.
   */
  P = *P_in;

  if (rounds > 0 &&
      !apply_ipa_folding_to_P(
          ctx, &P, L_vec, R_vec, u_flat, uinv_flat, rounds))
    goto cleanup;

  ok = pubkey_equal(ctx, &P, &RHS) ? 1 : 0;

cleanup:
  OPENSSL_cleanse(last, sizeof(last));

  if (u_flat)
    OPENSSL_cleanse(u_flat, rounds * kMPT_SCALAR_SIZE);
  if (uinv_flat)
    OPENSSL_cleanse(uinv_flat, rounds * kMPT_SCALAR_SIZE);
  if (G_scalars)
    OPENSSL_cleanse(G_scalars, total_points * kMPT_SCALAR_SIZE);
  if (H_scalars)
    OPENSSL_cleanse(H_scalars, total_points * kMPT_SCALAR_SIZE);
  if (dims)
    OPENSSL_cleanse(dims, rounds * sizeof(size_t));
  if (G_points)
    OPENSSL_cleanse(G_points, total_points * sizeof(secp256k1_pubkey));
  if (H_points)
    OPENSSL_cleanse(H_points, total_points * sizeof(secp256k1_pubkey));

  free(u_flat);
  free(uinv_flat);
  free(dims);
  free(G_points);
  free(H_points);
  free(G_scalars);
  free(H_scalars);

  return ok;
}

/**
 * Runs the Inner Product Argument (IPA) prover.
 * Recursively folds vectors G, H, a, and b into a single final term,
 * producing log2(n) pairs of cross-term commitments (stored in L_out/R_out).
 * Returns 1 on success, 0 on failure.
 */
int secp256k1_bulletproof_run_ipa_prover(
    const secp256k1_context *ctx, const secp256k1_pubkey *g,
    secp256k1_pubkey *G_vec, secp256k1_pubkey *H_vec, unsigned char *a_vec,
    unsigned char *b_vec, size_t n,
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE],
    const unsigned char ux_scalar[kMPT_SCALAR_SIZE], secp256k1_pubkey *L_out,
    secp256k1_pubkey *R_out, size_t max_rounds, size_t *rounds_out,
    unsigned char a_final[kMPT_SCALAR_SIZE],
    unsigned char b_final[kMPT_SCALAR_SIZE])
{
  size_t rounds = 0;
  size_t cur_n = n;
  int ok = 0;

  unsigned char u_scalar[kMPT_SCALAR_SIZE], u_inv[kMPT_SCALAR_SIZE];
  unsigned char last_challenge[kMPT_SCALAR_SIZE];

  /* Validate n is power of 2 */
  if (n == 0 || (n & (n - 1)) != 0)
    return 0;

  /* rounds = log2(n) */
  while (cur_n > 1)
  {
    cur_n >>= 1;
    rounds++;
  }
  cur_n = n;

  /* Bounds check (CRITICAL for aggregated proofs) */
  if (rounds > max_rounds)
    return 0;

  /* Seed transcript */
  memcpy(last_challenge, ipa_transcript_id, kMPT_SCALAR_SIZE);

  for (size_t r = 0; r < rounds; ++r)
  {
    size_t half_n = cur_n >> 1;
    secp256k1_pubkey Lr, Rr;

    /* 1) Compute cross-term commitments Lr, Rr */
    if (!secp256k1_bulletproof_ipa_compute_LR(
            ctx, &Lr, &Rr, a_vec, a_vec + half_n * kMPT_SCALAR_SIZE, b_vec,
            b_vec + half_n * kMPT_SCALAR_SIZE, G_vec, G_vec + half_n, H_vec,
            H_vec + half_n, g, ux_scalar, half_n))
      goto cleanup;

    /* 2) Store L/R */
    L_out[r] = Lr;
    R_out[r] = Rr;

    /* 3) Fiat–Shamir round challenge u_r */
    if (!derive_ipa_round_challenge(ctx, u_scalar, last_challenge, &Lr, &Rr))
      goto cleanup;

    /* 4) u_r^{-1} */
    if (!secp256k1_mpt_scalar_inverse(u_inv, u_scalar))
      goto cleanup;
    if (!secp256k1_ec_seckey_verify(ctx, u_inv))
      goto cleanup;

    /* 5) Update transcript chaining state */
    memcpy(last_challenge, u_scalar, kMPT_SCALAR_SIZE);

    /* 6) Fold vectors in-place */
    if (!secp256k1_bulletproof_ipa_compress_step(
            ctx, a_vec, b_vec, G_vec, H_vec, half_n, u_scalar, u_inv))
      goto cleanup;

    cur_n = half_n;
  }

  /* Final folded scalars */
  memcpy(a_final, a_vec, kMPT_SCALAR_SIZE);
  memcpy(b_final, b_vec, kMPT_SCALAR_SIZE);

  if (rounds_out)
    *rounds_out = rounds;
  ok = 1;

cleanup:
  OPENSSL_cleanse(u_scalar, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(u_inv, kMPT_SCALAR_SIZE);
  return ok;
}

/*
 * Verifies a Bulletproof Inner Product Argument (IPA).
 *
 * Given:
 *   - the original generator vectors G_vec and H_vec,
 *   - the prover’s cross-term commitments L_i and R_i,
 *   - the final folded scalars a_final and b_final,
 *   - the binding scalar ux,
 *   - and the initial commitment P,
 *
 * this function re-derives all Fiat–Shamir challenges u_i from the transcript
 * and reconstructs the folded generators G_f and H_f implicitly.
 *
 * Verification checks that the folded commitment P' equals:
 *
 *     P' = a_final * G_f
 *        + b_final * H_f
 *        + (a_final * b_final * ux) * U
 *
 * where G_f and H_f are obtained by folding G_vec and H_vec using the
 * challenges u_i and their inverses, and P' is obtained by applying the same
 * folding operations to P using the L_i and R_i commitments.
 *
 * All group operations avoid explicit construction of the point at infinity,
 * which is not representable via the libsecp256k1 public-key API.
 */
int ipa_verify_explicit(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec, /* original G generators (length n) */
    const secp256k1_pubkey *H_vec, /* original H generators (length n) */
    const secp256k1_pubkey *U, const secp256k1_pubkey *P_in, /* initial P */
    const secp256k1_pubkey *L_vec, /* length = rounds */
    const secp256k1_pubkey *R_vec, /* length = rounds */
    size_t n,                      /* total vector length (64*m) */
    const unsigned char a_final[kMPT_SCALAR_SIZE],
    const unsigned char b_final[kMPT_SCALAR_SIZE],
    const unsigned char ux[kMPT_SCALAR_SIZE],
    const unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE])
{
  secp256k1_pubkey P = *P_in;
  secp256k1_pubkey Gf, Hf, RHS, tmp;
  int RHS_inited = 0;
  int ok = 0;

  /* --- derive rounds --- */
  if (n == 0 || (n & (n - 1)) != 0)
    return 0;

  size_t rounds = bp_ipa_rounds(n);

  /* --- allocate u / u_inv --- */
  unsigned char *u_flat = (unsigned char *)malloc(rounds * kMPT_SCALAR_SIZE);
  unsigned char *uinv_flat = (unsigned char *)malloc(rounds * kMPT_SCALAR_SIZE);
  if (!u_flat || !uinv_flat)
    goto cleanup_alloc;

  unsigned char last[kMPT_SCALAR_SIZE];
  memcpy(last, ipa_transcript_id, kMPT_SCALAR_SIZE);

  /* ---- 1. Re-derive u_i ---- */
  for (size_t i = 0; i < rounds; i++)
  {
    unsigned char *ui = u_flat + kMPT_SCALAR_SIZE * i;
    unsigned char *uiinv = uinv_flat + kMPT_SCALAR_SIZE * i;

    if (!derive_ipa_round_challenge(ctx, ui, last, &L_vec[i], &R_vec[i]))
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(uiinv, ui))
      goto cleanup;
    if (!secp256k1_ec_seckey_verify(ctx, uiinv))
      goto cleanup;

    memcpy(last, ui, kMPT_SCALAR_SIZE);
  }

  /* ---- 2. Fold generators ---- */
  if (!fold_generators(ctx, &Gf, G_vec, u_flat, uinv_flat, n, rounds, 0))
    goto cleanup;

  if (!fold_generators(ctx, &Hf, H_vec, u_flat, uinv_flat, n, rounds, 1))
    goto cleanup;

  /* ---- 3. RHS = a*Gf + b*Hf + (a*b*ux)*U ---- */

  if (!scalar_is_zero(a_final))
  {
    tmp = Gf;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, a_final))
      goto cleanup;
    if (!add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }

  if (!scalar_is_zero(b_final))
  {
    tmp = Hf;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, b_final))
      goto cleanup;
    if (!add_term(ctx, &RHS, &RHS_inited, &tmp))
      goto cleanup;
  }

  {
    unsigned char ab[kMPT_SCALAR_SIZE], ab_ux[kMPT_SCALAR_SIZE];
    secp256k1_mpt_scalar_mul(ab, a_final, b_final);
    secp256k1_mpt_scalar_mul(ab_ux, ab, ux);

    if (!scalar_is_zero(ab_ux))
    {
      tmp = *U;
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmp, ab_ux))
        goto cleanup;
      if (!add_term(ctx, &RHS, &RHS_inited, &tmp))
        goto cleanup;
    }

    OPENSSL_cleanse(ab, kMPT_SCALAR_SIZE);
    OPENSSL_cleanse(ab_ux, kMPT_SCALAR_SIZE);
  }

  if (!RHS_inited)
    goto cleanup;

  /* ---- 4. Fold P using L/R ---- */
  if (!apply_ipa_folding_to_P(ctx, &P, L_vec, R_vec, u_flat, uinv_flat, rounds))
    goto cleanup;

  /* ---- 5. Compare P and RHS ---- */
  if (pubkey_equal(ctx, &P, &RHS))
    ok = 1;

cleanup:
  OPENSSL_cleanse(u_flat, rounds * kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(uinv_flat, rounds * kMPT_SCALAR_SIZE);

cleanup_alloc:
  free(u_flat);
  free(uinv_flat);
  return ok;
}
/**
 * Phase 1, Step 3 (Aggregated):
 * Compute al, ar, sl, sr vectors for ONE value block inside an aggregated
 * proof.
 *
 * The caller is responsible for:
 *   - allocating al/ar/sl/sr of length (BP_VALUE_BITS * m)
 *   - calling this once per value with block_index = j
 *
 * Block layout:
 *   bits for value j occupy indices:
 *     [BP_VALUE_BITS * j .. BP_VALUE_BITS * j + BP_VALUE_BITS - 1]
 */
int secp256k1_bulletproof_compute_vectors_block(
    const secp256k1_context *ctx, uint64_t value,
    size_t block_index, /* j-th value */
    unsigned char *al,  /* length = BP_TOTAL_BITS(m) * 32 */
    unsigned char *ar, unsigned char *sl, unsigned char *sr)
{
  const size_t offset = BP_VALUE_BITS * block_index;

  /* Scalars */
  unsigned char one[kMPT_SCALAR_SIZE] = {0};
  unsigned char minus_one[kMPT_SCALAR_SIZE];

  one[kMPT_SCALAR_SIZE - 1] = 1;
  memcpy(minus_one, one, kMPT_SCALAR_SIZE);
  secp256k1_mpt_scalar_negate(minus_one, minus_one);

  /* ---- 1. Encode value bits into al/ar ---- */
  for (size_t i = 0; i < BP_VALUE_BITS; i++)
  {
    size_t idx = offset + i;
    unsigned char bit = (unsigned char)((value >> i) & 1);
    unsigned char mask =
        (unsigned char)(-bit); /* 0xFF if bit==1, 0x00 if bit==0 */

    for (int b = 0; b < (int)kMPT_SCALAR_SIZE; b++)
    {
      al[idx * kMPT_SCALAR_SIZE + b] = one[b] & mask;
      ar[idx * kMPT_SCALAR_SIZE + b] = minus_one[b] & ~mask;
    }
  }
  /* ---- 2. Generate random blinding vectors sl/sr ---- */
  for (size_t i = 0; i < BP_VALUE_BITS; i++)
  {
    size_t idx = offset + i;

    if (!generate_random_scalar(ctx, sl + idx * kMPT_SCALAR_SIZE))
    {
      goto cleanup;
    }
    if (!generate_random_scalar(ctx, sr + idx * kMPT_SCALAR_SIZE))
    {
      goto cleanup;
    }
  }

  return 1;

cleanup:
  /* Wipe only the affected block */
  OPENSSL_cleanse(al + offset * kMPT_SCALAR_SIZE,
                  BP_VALUE_BITS * kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(ar + offset * kMPT_SCALAR_SIZE,
                  BP_VALUE_BITS * kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(sl + offset * kMPT_SCALAR_SIZE,
                  BP_VALUE_BITS * kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(sr + offset * kMPT_SCALAR_SIZE,
                  BP_VALUE_BITS * kMPT_SCALAR_SIZE);
  return 0;
}
/**
 * Computes the Pedersen Commitment: C = value*G + blinding_factor*Pk_base.
 */
int secp256k1_bulletproof_create_commitment(
    const secp256k1_context *ctx, secp256k1_pubkey *commitment_C,
    uint64_t value, const unsigned char *blinding_factor,
    const secp256k1_pubkey *h_generator)
{
  secp256k1_pubkey G_term, Pk_term;
  const secp256k1_pubkey *points_to_add[2];
  int v_is_zero = (value == 0);

  /* 1. Compute r * h_generator (The Blinding Term) */
  Pk_term = *h_generator;
  if (mpt_ct_pubkey_tweak_mul(ctx, &Pk_term, blinding_factor) != 1)
    return 0;

  /* 2. Handle Value Term */
  if (v_is_zero)
  {
    /* If v=0, C = 0*G + r*H = r*H.
       We skip G_term entirely because libsecp cannot represent infinity. */
    *commitment_C = Pk_term;
    return 1;
  }

  /* 3. Compute v * G (The Value Term) */
  if (!compute_amount_point(ctx, &G_term, value))
    return 0;

  /* 4. Combine: C = v*G + r*Pk_base */
  points_to_add[0] = &G_term;
  points_to_add[1] = &Pk_term;
  if (secp256k1_ec_pubkey_combine(ctx, commitment_C, points_to_add, 2) != 1)
    return 0;

  return 1;
}

/* Helper for a vector 0 */
static int scalar_vector_all_zero(const unsigned char *scalars, size_t n)
{
  unsigned char zero[kMPT_SCALAR_SIZE] = {0};
  for (size_t i = 0; i < n; ++i)
  {
    if (memcmp(scalars + kMPT_SCALAR_SIZE * i, zero, kMPT_SCALAR_SIZE) != 0)
      return 0; /* found non-zero */
  }
  return 1; /* all zero */
}

/* Helper to calculate commitment terms like A and S */
static int calculate_commitment_term(
    const secp256k1_context *ctx, secp256k1_pubkey *out,
    const secp256k1_pubkey *h_generator, const unsigned char *base_scalar,
    const unsigned char *vec_l, const unsigned char *vec_r,
    const secp256k1_pubkey *G_vec, const secp256k1_pubkey *H_vec, size_t n)
{
  secp256k1_pubkey tG, tH, tB;
  const secp256k1_pubkey *pts[3];
  int n_pts = 0;

  /* 1. base_scalar * Base */
  tB = *h_generator;
  if (!mpt_ct_pubkey_tweak_mul(ctx, &tB, base_scalar))
    return 0;
  pts[n_pts++] = &tB;

  /* 2. <vec_l, G> */
  if (!scalar_vector_all_zero(vec_l, n))
  {
    if (!secp256k1_bulletproof_ipa_msm(ctx, &tG, G_vec, vec_l, n))
      return 0; /* REAL FAILURE */
    pts[n_pts++] = &tG;
  }

  /* 3. <vec_r, H> */
  if (!scalar_vector_all_zero(vec_r, n))
  {
    if (!secp256k1_bulletproof_ipa_msm(ctx, &tH, H_vec, vec_r, n))
      return 0; /* REAL FAILURE */
    pts[n_pts++] = &tH;
  }

  if (n_pts == 1)
  {
    *out = *pts[0];
    return 1;
  }

  if (!secp256k1_ec_pubkey_combine(ctx, out, pts, n_pts))
    return 0;

  return 1;
}

/**
 * Generates an aggregated Bulletproof for m values.
 *
 * This function constructs a range proof asserting that all m values are within
 * the [0, 2^64) range. The proof is serialized into proof_out.
 *
 * Inputs:
 * - values: Array of m 64-bit integers to prove.
 * - blindings_flat: Array of m 32-byte blinding factors (one per value).
 * - m: Number of values to aggregate (must be a power of 2).
 * - h_generator: Generator H used for the commitments (C = vG + rH).
 * - context_id: Optional 32-byte unique ID to bind the proof to a context.
 *
 * Outputs:
 * - proof_out: Buffer to receive the serialized proof.
 * - proof_len: On input, size of proof_out. On output, actual proof size.
 *
 * Returns 1 on success, 0 on failure.
 */
int secp256k1_bulletproof_prove_agg(
    const secp256k1_context *ctx, unsigned char *proof_out, size_t *proof_len,
    const uint64_t *values, const unsigned char *blindings_flat, size_t m,
    const secp256k1_pubkey *h_generator, const unsigned char *context_id)
{
  /* ---- 0. Dimensions ---- */
  const size_t n = BP_TOTAL_BITS(m);          /* 64*m */
  const size_t rounds = bp_ipa_rounds_3w(n); /* ceil(log_3(64*m)) with dynamic padding */

  /* 64*m must be power-of-two -> m must be power-of-two */
  if (m == 0 || m > BP_MAX_VALUES)
    return 0;
  if ((n & (n - 1)) != 0)
    return 0;

  /* Pure 3W proof length = 4*33 + 4*rounds*33 + 5*32. */
  
  const size_t proof_size = 292 + 132 * rounds;

  /*
  * proof_len is input capacity when proof_out != NULL.
  * Do not overwrite it before checking the caller's buffer.
  */
  if (proof_len == NULL)
     return 0;

  /* Size-query mode. */
  if (proof_out == NULL)
  {
      *proof_len = proof_size;
      return 1;
  }

  /* Caller supplied a buffer that is too small. */
  if (*proof_len < proof_size)
  {
      *proof_len = proof_size;
      return 0;
  }

  int ok = 0;

  /* ---- 1. Allocate vectors ---- */
  secp256k1_pubkey *G_vec =
      (secp256k1_pubkey *)malloc(n * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *H_vec =
      (secp256k1_pubkey *)malloc(n * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *H_prime =
      (secp256k1_pubkey *)malloc(n * sizeof(secp256k1_pubkey));
  unsigned char *al = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  unsigned char *ar = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  unsigned char *sl = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  unsigned char *sr = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  unsigned char *l_vec = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  unsigned char *r_vec = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  unsigned char *r1_vec = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);

  secp256k1_pubkey *L1_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *L2_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *R1_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *R2_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));

  unsigned char *y_powers =
      (unsigned char *)malloc(n * kMPT_SCALAR_SIZE); /* y^i */
  unsigned char *z_j2 =
      (unsigned char *)malloc(m * kMPT_SCALAR_SIZE); /* z^(j+2) */

  if (!G_vec || !H_vec || !H_prime || !al || !ar || !sl || !sr || !l_vec ||
      !r_vec || !r1_vec || !L1_vec || !L2_vec || !R1_vec || !R2_vec ||
      !y_powers || !z_j2)
  {
    goto cleanup;
  }

  /* ---- 2. Scalars / points ---- */
  secp256k1_pubkey A, S, T1, T2, U;

  unsigned char alpha[kMPT_SCALAR_SIZE], rho[kMPT_SCALAR_SIZE];
  unsigned char tau1[kMPT_SCALAR_SIZE], tau2[kMPT_SCALAR_SIZE];
  unsigned char t1[kMPT_SCALAR_SIZE], t2[kMPT_SCALAR_SIZE];
  unsigned char t_hat[kMPT_SCALAR_SIZE], tau_x[kMPT_SCALAR_SIZE],
      mu[kMPT_SCALAR_SIZE];
  unsigned char a_final[kMPT_SCALAR_SIZE], b_final[kMPT_SCALAR_SIZE];

  unsigned char y[kMPT_SCALAR_SIZE], z[kMPT_SCALAR_SIZE], x[kMPT_SCALAR_SIZE];
  unsigned char z_sq[kMPT_SCALAR_SIZE], z_neg[kMPT_SCALAR_SIZE],
      x_sq[kMPT_SCALAR_SIZE];
  unsigned char ux_scalar[kMPT_SCALAR_SIZE];
  unsigned char ipa_transcript[kMPT_SCALAR_SIZE];

  unsigned char one[kMPT_SCALAR_SIZE] = {0};
  one[kMPT_SCALAR_SIZE - 1] = 1;
  unsigned char minus_one[kMPT_SCALAR_SIZE];
  secp256k1_mpt_scalar_negate(minus_one, one);
  unsigned char zero[kMPT_SCALAR_SIZE] = {0};

  /* ---- 3. Generator vectors ---- */
  if (!secp256k1_mpt_get_generator_vector(ctx, G_vec, n,
                                          (const unsigned char *)"BP_G", 4))
    goto cleanup;
  if (!secp256k1_mpt_get_generator_vector(ctx, H_vec, n,
                                          (const unsigned char *)"BP_H", 4))
    goto cleanup;
  {
    secp256k1_pubkey U_arr[1];
    if (!secp256k1_mpt_get_generator_vector(ctx, U_arr, 1,
                                            (const unsigned char *)"BP_U", 4))
      goto cleanup;
    U = U_arr[0];
  }

  /* ---- 4. Bit-decomposition for m values into al/ar (concat) + random sl/sr
   * ---- */
  for (size_t j = 0; j < m; j++)
  {
    uint64_t v = values[j];
    for (size_t i = 0; i < BP_VALUE_BITS; i++)
    {
      const size_t k = j * BP_VALUE_BITS + i; /* 0..n-1 */
      unsigned char *al_k = al + kMPT_SCALAR_SIZE * k;
      unsigned char *ar_k = ar + kMPT_SCALAR_SIZE * k;
      unsigned char *sl_k = sl + kMPT_SCALAR_SIZE * k;
      unsigned char *sr_k = sr + kMPT_SCALAR_SIZE * k;

      /* Constant-time bit decomposition to prevent cache-timing leaks */
      unsigned char bit = (unsigned char)((v >> i) & 1);
      unsigned char mask =
          (unsigned char)(0 - bit); /* 0xFF if bit==1, 0x00 if bit==0 */

      for (int b = 0; b < (int)kMPT_SCALAR_SIZE; b++)
      {
        al_k[b] = one[b] & mask;
        ar_k[b] = minus_one[b] & ~mask;
      }

      if (!generate_random_scalar(ctx, sl_k))
        goto cleanup;
      if (!generate_random_scalar(ctx, sr_k))
        goto cleanup;
    }
  }

  if (!generate_random_scalar(ctx, alpha))
    goto cleanup;
  if (!generate_random_scalar(ctx, rho))
    goto cleanup;

  /* ---- 5. Commitments A and S ----
   * A = alpha*Base + <al,G> + <ar,H>
   * S = rho*Base   + <sl,G> + <sr,H>
   */
  if (!calculate_commitment_term(ctx, &A, h_generator, alpha, al, ar, G_vec,
                                 H_vec, n))
    goto cleanup;
  if (!calculate_commitment_term(ctx, &S, h_generator, rho, sl, sr, G_vec,
                                 H_vec, n))
    goto cleanup;

  /* ---- 6. Fiat–Shamir y,z ---- */
  /*
   * T_0 = domain || gens_digest || N (BE u32) || m (BE u32) || V_0..V_{m-1}
   * T_1 = T_0 || A || S
   *   y = H(T_1 || context_id)
   *   z = H(T_1 || y || context_id)
   *
   * gens_digest binds the BP fixed generators (H, G_vec, H_vec) into the
   * transcript per the spec.  N (= BP_VALUE_BITS) and m (= aggregation
   * count) are explicit so the verifier cannot be confused into accepting
   * a proof produced for a different range / aggregation parameter.
   * (CMPT appendix.tex, "Fiat-Shamir Challenges".)
   */
  {
    unsigned char A_ser[kMPT_PUBKEY_SIZE], S_ser[kMPT_PUBKEY_SIZE];
    unsigned char gens_digest[kMPT_HALF_SHA_SIZE];
    unsigned char N_be[4], m_be[4];
    size_t len;
    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    int fs_ok = 1;

    if (!mdctx)
      goto cleanup;

    if (!bulletproof_gens_digest(ctx, h_generator, G_vec, H_vec, n,
                                 gens_digest))
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    bulletproof_be32_encode(N_be, (uint32_t)BP_VALUE_BITS);
    bulletproof_be32_encode(m_be, (uint32_t)m);

    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, A_ser, &len, &A,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }

    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, S_ser, &len, &S,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }

    // y = H(domain || gens || N || m || V* || A || S || context)
    if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, "MPT_BULLETPROOF_RANGE", 21) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, gens_digest, 32) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, N_be, 4) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, m_be, 4) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }

    for (size_t i = 0; i < m; i++)
    {
      secp256k1_pubkey V_temp;
      unsigned char V_ser[kMPT_PUBKEY_SIZE];
      size_t v_len = kMPT_PUBKEY_SIZE;
      if (!secp256k1_bulletproof_create_commitment(
              ctx, &V_temp, values[i], blindings_flat + kMPT_SCALAR_SIZE * i,
              h_generator))
      {
        fs_ok = 0;
        goto fs_cleanup;
      }
      if (!secp256k1_ec_pubkey_serialize(ctx, V_ser, &v_len, &V_temp,
                                         SECP256K1_EC_COMPRESSED) ||
          v_len != kMPT_PUBKEY_SIZE)
      {
        fs_ok = 0;
        goto fs_cleanup;
      }
      if (EVP_DigestUpdate(mdctx, V_ser, kMPT_PUBKEY_SIZE) != 1)
      {
        fs_ok = 0;
        goto fs_cleanup;
      }
    }

    if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (context_id &&
        EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestFinal_ex(mdctx, y, NULL) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    secp256k1_mpt_scalar_reduce32(y, y);

    // z = H(domain || gens || N || m || V* || A || S || y || context)
    if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, "MPT_BULLETPROOF_RANGE", 21) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, gens_digest, 32) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, N_be, 4) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, m_be, 4) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }

    for (size_t i = 0; i < m; i++)
    {
      secp256k1_pubkey V_temp;
      unsigned char V_ser[kMPT_PUBKEY_SIZE];
      size_t v_len = kMPT_PUBKEY_SIZE;
      if (!secp256k1_bulletproof_create_commitment(
              ctx, &V_temp, values[i], blindings_flat + kMPT_SCALAR_SIZE * i,
              h_generator))
      {
        fs_ok = 0;
        goto fs_cleanup;
      }
      if (!secp256k1_ec_pubkey_serialize(ctx, V_ser, &v_len, &V_temp,
                                         SECP256K1_EC_COMPRESSED) ||
          v_len != kMPT_PUBKEY_SIZE)
      {
        fs_ok = 0;
        goto fs_cleanup;
      }
      if (EVP_DigestUpdate(mdctx, V_ser, kMPT_PUBKEY_SIZE) != 1)
      {
        fs_ok = 0;
        goto fs_cleanup;
      }
    }

    if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestUpdate(mdctx, y, kMPT_SCALAR_SIZE) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (context_id &&
        EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    if (EVP_DigestFinal_ex(mdctx, z, NULL) != 1)
    {
      fs_ok = 0;
      goto fs_cleanup;
    }
    secp256k1_mpt_scalar_reduce32(z, z);

    memcpy(z_neg, z, kMPT_SCALAR_SIZE);
    secp256k1_mpt_scalar_negate(z_neg, z_neg);

  fs_cleanup:
    EVP_MD_CTX_free(mdctx);
    if (!fs_ok)
      goto cleanup;
  }

  /* ---- 7. Aggregated polynomial setup ---- */

  /* y_powers[k] = y^k */
  {
    unsigned char ypow[kMPT_SCALAR_SIZE];
    memcpy(ypow, one, kMPT_SCALAR_SIZE);

    for (size_t k = 0; k < n; k++)
    {
      memcpy(y_powers + kMPT_SCALAR_SIZE * k, ypow, kMPT_SCALAR_SIZE);
      secp256k1_mpt_scalar_mul(ypow, ypow, y);
    }
    OPENSSL_cleanse(ypow, kMPT_SCALAR_SIZE);
  }

  /* z_j2[j] = z^(j+2) */
  compute_z_pows_j2(ctx, (unsigned char (*)[kMPT_SCALAR_SIZE])z_j2, z, m);

  /* l0, r0, r1 */
  for (size_t block = 0; block < m; block++)
  {
    const unsigned char *zblk =
        z_j2 + kMPT_SCALAR_SIZE * block; /* z^(block+2) */

    for (size_t i = 0; i < BP_VALUE_BITS; i++)
    {
      size_t k = block * BP_VALUE_BITS + i;

      unsigned char *l0 = l_vec + kMPT_SCALAR_SIZE * k;
      unsigned char *r0 = r_vec + kMPT_SCALAR_SIZE * k;
      unsigned char *r1 = r1_vec + kMPT_SCALAR_SIZE * k;

      const unsigned char *al_k = al + kMPT_SCALAR_SIZE * k;
      const unsigned char *ar_k = ar + kMPT_SCALAR_SIZE * k;
      const unsigned char *sr_k = sr + kMPT_SCALAR_SIZE * k;
      const unsigned char *yk = y_powers + kMPT_SCALAR_SIZE * k;

      unsigned char two_i[kMPT_SCALAR_SIZE] = {0};
      two_i[31 - (i >> 3)] = (unsigned char)(1u << (i & 7));

      /* l0 = aL - z */
      secp256k1_mpt_scalar_add(l0, al_k, z_neg);

      /* r0 = y^k * (aR + z) + z^(block+2) * 2^i */
      {
        unsigned char tmp1[kMPT_SCALAR_SIZE], tmp2[kMPT_SCALAR_SIZE];

        /* tmp1 = aR + z */
        secp256k1_mpt_scalar_add(tmp1, ar_k, z);

        /* r0 = y^k * tmp1 */
        secp256k1_mpt_scalar_mul(r0, tmp1, yk);

        /* tmp2 = z^(block+2) * 2^i */
        secp256k1_mpt_scalar_mul(tmp2, zblk, two_i);

        /* r0 += tmp2 */
        secp256k1_mpt_scalar_add(r0, r0, tmp2);

        OPENSSL_cleanse(tmp1, kMPT_SCALAR_SIZE);
        OPENSSL_cleanse(tmp2, kMPT_SCALAR_SIZE);
      }

      /* r1 = sR * y^k */
      secp256k1_mpt_scalar_mul(r1, sr_k, yk);
    }
  }

  /* t1 = <l0, r1> + <l1, r0> */
  {
    unsigned char dot1[kMPT_SCALAR_SIZE], dot2[kMPT_SCALAR_SIZE];
    if (!secp256k1_bulletproof_ipa_dot(ctx, dot1, l_vec, r1_vec, n))
      goto cleanup;
    if (!secp256k1_bulletproof_ipa_dot(ctx, dot2, sl, r_vec, n))
      goto cleanup;
    secp256k1_mpt_scalar_add(t1, dot1, dot2);
    OPENSSL_cleanse(dot1, kMPT_SCALAR_SIZE);
    OPENSSL_cleanse(dot2, kMPT_SCALAR_SIZE);
  }

  /* t2 = <l1, r1> */
  if (!secp256k1_bulletproof_ipa_dot(ctx, t2, sl, r1_vec, n))
    goto cleanup;

  /* Make sure these exist before T1/T2 */
  if (!generate_random_scalar(ctx, tau1))
    goto cleanup;
  if (!generate_random_scalar(ctx, tau2))
    goto cleanup;

  /* ---- 8. Commit T1, T2 ---- */
  /* T1 = t1*G + tau1*Base   where G = G_vec[0].
   * When t1 == 0 the t1*G term is the point at infinity (which libsecp256k1
   * cannot emit), so commit T1 = tau1*Base directly. */
  {
    secp256k1_pubkey tG, tB;
    const secp256k1_pubkey *pts[2];

    tB = *h_generator;
    if (!mpt_ct_pubkey_tweak_mul(ctx, &tB, tau1))
      goto cleanup;

    if (memcmp(t1, zero, kMPT_SCALAR_SIZE) == 0)
    {
      T1 = tB;
    }
    else
    {
      if (!secp256k1_ec_pubkey_create(ctx, &tG, t1))
        goto cleanup;
      pts[0] = &tG;
      pts[1] = &tB;
      if (!secp256k1_ec_pubkey_combine(ctx, &T1, pts, 2))
        goto cleanup;
    }
  }

  /* T2 = t2*G + tau2*Base. Same t2==0 short-circuit as above. */
  {
    secp256k1_pubkey tG, tB;
    const secp256k1_pubkey *pts[2];

    tB = *h_generator;
    if (!mpt_ct_pubkey_tweak_mul(ctx, &tB, tau2))
      goto cleanup;

    if (memcmp(t2, zero, kMPT_SCALAR_SIZE) == 0)
    {
      T2 = tB;
    }
    else
    {
      if (!secp256k1_ec_pubkey_create(ctx, &tG, t2))
        goto cleanup;
      pts[0] = &tG;
      pts[1] = &tB;
      if (!secp256k1_ec_pubkey_combine(ctx, &T2, pts, 2))
        goto cleanup;
    }
  }

  /* ---- 9. Challenge x ---- */
  /* x = H(A || S || y || z || T1 || T2 || context_id) */
  {
    unsigned char A_ser[kMPT_PUBKEY_SIZE], S_ser[kMPT_PUBKEY_SIZE],
        T1_ser[kMPT_PUBKEY_SIZE], T2_ser[kMPT_PUBKEY_SIZE];
    size_t len;
    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    int fs_ok = 0;

    if (!mdctx)
      goto cleanup;

    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, A_ser, &len, &A,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto fs_x_cleanup;
    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, S_ser, &len, &S,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto fs_x_cleanup;
    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, T1_ser, &len, &T1,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto fs_x_cleanup;
    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, T2_ser, &len, &T2,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto fs_x_cleanup;

    if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
      goto fs_x_cleanup;
    if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_x_cleanup;
    if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_x_cleanup;
    if (EVP_DigestUpdate(mdctx, y, kMPT_SCALAR_SIZE) != 1)
      goto fs_x_cleanup;
    if (EVP_DigestUpdate(mdctx, z, kMPT_SCALAR_SIZE) != 1)
      goto fs_x_cleanup;
    if (EVP_DigestUpdate(mdctx, T1_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_x_cleanup;
    if (EVP_DigestUpdate(mdctx, T2_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_x_cleanup;
    if (context_id &&
        EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
      goto fs_x_cleanup;
    if (EVP_DigestFinal_ex(mdctx, x, NULL) != 1)
      goto fs_x_cleanup;

    secp256k1_mpt_scalar_reduce32(x, x);
    if (memcmp(x, zero, kMPT_SCALAR_SIZE) == 0)
      goto fs_x_cleanup; /* avoid infinity later */

    fs_ok = 1;

  fs_x_cleanup:
    EVP_MD_CTX_free(mdctx);
    if (!fs_ok)
      goto cleanup;
  }

  /* ---- 10. Evaluate l(x), r(x), t_hat ---- */
  for (size_t k = 0; k < n; k++)
  {
    unsigned char tmp[kMPT_SCALAR_SIZE];

    /* l = l0 + sL*x */
    secp256k1_mpt_scalar_mul(tmp, sl + kMPT_SCALAR_SIZE * k, x);
    secp256k1_mpt_scalar_add(l_vec + kMPT_SCALAR_SIZE * k,
                             l_vec + kMPT_SCALAR_SIZE * k, tmp);

    /* r = r0 + r1*x */
    secp256k1_mpt_scalar_mul(tmp, r1_vec + kMPT_SCALAR_SIZE * k, x);
    secp256k1_mpt_scalar_add(r_vec + kMPT_SCALAR_SIZE * k,
                             r_vec + kMPT_SCALAR_SIZE * k, tmp);

    OPENSSL_cleanse(tmp, kMPT_SCALAR_SIZE);
  }

  if (!secp256k1_bulletproof_ipa_dot(ctx, t_hat, l_vec, r_vec, n))
    goto cleanup;

  /* ---- 11. tau_x and mu (aggregation changes tau_x) ---- */
  secp256k1_mpt_scalar_mul(x_sq, x, x);

  /* tau_x = tau2*x^2 + tau1*x + sum_j z^(j+2) * blinding_j */
  secp256k1_mpt_scalar_mul(tau_x, tau2, x_sq);
  {
    unsigned char tmp[kMPT_SCALAR_SIZE];
    secp256k1_mpt_scalar_mul(tmp, tau1, x);
    secp256k1_mpt_scalar_add(tau_x, tau_x, tmp);

    /* + sum_j z^(j+2) * r_j */
    for (size_t j = 0; j < m; j++)
    {
      unsigned char add[kMPT_SCALAR_SIZE];
      secp256k1_mpt_scalar_mul(add, z_j2 + kMPT_SCALAR_SIZE * j,
                               blindings_flat + kMPT_SCALAR_SIZE * j);
      secp256k1_mpt_scalar_add(tau_x, tau_x, add);
      OPENSSL_cleanse(add, kMPT_SCALAR_SIZE);
    }

    OPENSSL_cleanse(tmp, kMPT_SCALAR_SIZE);
  }

  /* mu = alpha + rho*x */
  {
    unsigned char tmp[kMPT_SCALAR_SIZE];
    secp256k1_mpt_scalar_mul(tmp, rho, x);
    secp256k1_mpt_scalar_add(mu, alpha, tmp);
    OPENSSL_cleanse(tmp, kMPT_SCALAR_SIZE);
  }

  /* ---- 12. IPA transcript + ux (binding), and H' normalization ---- */

  /* 12a. Build a stable IPA transcript seed (32 bytes).
   *
   * IMPORTANT:
   *  - Prover and verifier MUST hash the exact same bytes in the exact same
   * order.
   *  - Use only public elements that both sides already know.
   *  - Do NOT depend on internal intermediate buffers.
   *
   * Minimal, safe choice: A||S||T1||T2 || y||z||x || t_hat || context_id
   * (All points are serialized compressed 33 bytes.)
   */
  {
    unsigned char A_ser[kMPT_PUBKEY_SIZE], S_ser[kMPT_PUBKEY_SIZE],
        T1_ser[kMPT_PUBKEY_SIZE], T2_ser[kMPT_PUBKEY_SIZE];
    size_t ser_len;
    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    int fs_ok = 0;

    if (!mdctx)
      goto cleanup;

    ser_len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, A_ser, &ser_len, &A,
                                       SECP256K1_EC_COMPRESSED) ||
        ser_len != kMPT_PUBKEY_SIZE)
      goto fs_ipa_cleanup;

    ser_len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, S_ser, &ser_len, &S,
                                       SECP256K1_EC_COMPRESSED) ||
        ser_len != kMPT_PUBKEY_SIZE)
      goto fs_ipa_cleanup;

    ser_len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, T1_ser, &ser_len, &T1,
                                       SECP256K1_EC_COMPRESSED) ||
        ser_len != kMPT_PUBKEY_SIZE)
      goto fs_ipa_cleanup;

    ser_len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, T2_ser, &ser_len, &T2,
                                       SECP256K1_EC_COMPRESSED) ||
        ser_len != kMPT_PUBKEY_SIZE)
      goto fs_ipa_cleanup;

    if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, "MPT_BP_IPA_3W", 13) != 1)
      goto fs_ipa_cleanup;

    if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, T1_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, T2_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, y, kMPT_SCALAR_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, z, kMPT_SCALAR_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, x, kMPT_SCALAR_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (EVP_DigestUpdate(mdctx, t_hat, kMPT_SCALAR_SIZE) != 1)
      goto fs_ipa_cleanup;
    if (context_id &&
        EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
      goto fs_ipa_cleanup;

    if (EVP_DigestFinal_ex(mdctx, ipa_transcript, NULL) != 1)
      goto fs_ipa_cleanup;

    fs_ok = 1;

  fs_ipa_cleanup:
    EVP_MD_CTX_free(mdctx);
    if (!fs_ok)
      goto cleanup;
  }

  /* 12b. Derive u_x = H(ipa_transcript || t_hat) reduced to scalar. */
  if (!derive_ipa_binding_challenge(ctx, ux_scalar, ipa_transcript, t_hat))
    goto cleanup;

  /* 12c. Normalize H: H'[k] = H[k] * y^{-k}.
   *
   * NOTE:
   *  - Requires y != 0.
   *  - If y==0 (mod q), abort (cannot invert).
   */
  {
    unsigned char y_inv[kMPT_SCALAR_SIZE];
    unsigned char y_inv_pow[kMPT_SCALAR_SIZE]; /* (y^{-1})^k */
    if (memcmp(y, zero, kMPT_SCALAR_SIZE) == 0)
      goto cleanup;

    if (!secp256k1_mpt_scalar_inverse(y_inv, y))
      goto cleanup;
    memcpy(y_inv_pow, one, kMPT_SCALAR_SIZE);

    for (size_t k = 0; k < n; k++)
    {
      H_prime[k] = H_vec[k];
      /* H_prime[k] = H_vec[k] * (y^{-1})^k */
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &H_prime[k], y_inv_pow))
        goto cleanup;
      secp256k1_mpt_scalar_mul(y_inv_pow, y_inv_pow, y_inv);
    }

    OPENSSL_cleanse(y_inv, kMPT_SCALAR_SIZE);
    OPENSSL_cleanse(y_inv_pow, kMPT_SCALAR_SIZE);
  }

  /* 12d. Run IPA prover */
  {
    size_t rounds_used = 0;

    if (!secp256k1_bulletproof_run_ipa_prover_3w(
            ctx, &U,           /* binding generator point */
            G_vec,             /* G */
            H_prime,           /* H' */
            l_vec,             /* l(x) scalars */
            r_vec,             /* r(x) scalars */
            n, ipa_transcript, /* 32-byte seed */
            ux_scalar,         /* u_x scalar */
            L1_vec, L2_vec, R1_vec, R2_vec, rounds,
            &rounds_used, a_final, b_final))
      goto cleanup;

    if (rounds_used != rounds)
      goto cleanup;
  }

  /* ---- 13. Serialize (uses rounds) ---- */
  {
    const size_t expected = 292 + 132 * rounds; /* 4*33 + 4*rounds*33 + 5*32 */

    /* Standard pattern: query size only */
    if (proof_out == NULL)
    {
      if (proof_len)
        *proof_len = expected;
      ok = 1;
      goto cleanup;
    }

    if (proof_len == NULL)
      goto cleanup;

    if (*proof_len < expected)
    {
      *proof_len = expected;
      goto cleanup; /* not enough space */
    }

    unsigned char *ptr = proof_out;
    size_t ser_len;

#define SER_PT(P)                                                              \
  do                                                                           \
  {                                                                            \
    ser_len = kMPT_PUBKEY_SIZE;                                                \
    if (!secp256k1_ec_pubkey_serialize(ctx, ptr, &ser_len, &(P),               \
                                       SECP256K1_EC_COMPRESSED))               \
      goto cleanup;                                                            \
    if (ser_len != kMPT_PUBKEY_SIZE)                                           \
      goto cleanup;                                                            \
    ptr += kMPT_PUBKEY_SIZE;                                                   \
  } while (0)

    SER_PT(A);
    SER_PT(S);
    SER_PT(T1);
    SER_PT(T2);

    /* Round-major 3W serialization: L1,L2,R1,R2 for each round. */
    for (size_t r = 0; r < rounds; r++)
    {
      SER_PT(L1_vec[r]);
      SER_PT(L2_vec[r]);
      SER_PT(R1_vec[r]);
      SER_PT(R2_vec[r]);
    }

    memcpy(ptr, a_final, kMPT_SCALAR_SIZE);
    ptr += kMPT_SCALAR_SIZE;
    memcpy(ptr, b_final, kMPT_SCALAR_SIZE);
    ptr += kMPT_SCALAR_SIZE;
    memcpy(ptr, t_hat, kMPT_SCALAR_SIZE);
    ptr += kMPT_SCALAR_SIZE;
    memcpy(ptr, tau_x, kMPT_SCALAR_SIZE);
    ptr += kMPT_SCALAR_SIZE;
    memcpy(ptr, mu, kMPT_SCALAR_SIZE);
    ptr += kMPT_SCALAR_SIZE;

#undef SER_PT

    /* Final sanity */
    if ((size_t)(ptr - proof_out) != expected)
      goto cleanup;

    *proof_len = expected;
  }

  ok = 1;

cleanup:

  /* wipe sensitive scalars; free buffers */
  if (al)
    OPENSSL_cleanse(al, n * kMPT_SCALAR_SIZE);
  if (ar)
    OPENSSL_cleanse(ar, n * kMPT_SCALAR_SIZE);
  if (sl)
    OPENSSL_cleanse(sl, n * kMPT_SCALAR_SIZE);
  if (sr)
    OPENSSL_cleanse(sr, n * kMPT_SCALAR_SIZE);
  if (l_vec)
    OPENSSL_cleanse(l_vec, n * kMPT_SCALAR_SIZE);
  if (r_vec)
    OPENSSL_cleanse(r_vec, n * kMPT_SCALAR_SIZE);
  if (r1_vec)
    OPENSSL_cleanse(r1_vec, n * kMPT_SCALAR_SIZE);

  OPENSSL_cleanse(alpha, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(rho, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(tau1, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(tau2, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(t1, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(t2, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(t_hat, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(tau_x, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(mu, kMPT_SCALAR_SIZE);

  OPENSSL_cleanse(y, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(z, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(x, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(z_sq, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(z_neg, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(x_sq, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(ux_scalar, kMPT_SCALAR_SIZE);
  OPENSSL_cleanse(ipa_transcript, kMPT_SCALAR_SIZE);

  if (G_vec)
  {
    OPENSSL_cleanse(G_vec, n * sizeof(secp256k1_pubkey));
    free(G_vec);
  }
  if (H_vec)
  {
    OPENSSL_cleanse(H_vec, n * sizeof(secp256k1_pubkey));
    free(H_vec);
  }
  if (H_prime)
  {
    OPENSSL_cleanse(H_prime, n * sizeof(secp256k1_pubkey));
    free(H_prime);
  }

  free(al);
  free(ar);
  free(sl);
  free(sr);
  free(l_vec);
  free(r_vec);
  free(r1_vec);

  if (L1_vec)
  {
    OPENSSL_cleanse(L1_vec, rounds * sizeof(secp256k1_pubkey));
    free(L1_vec);
  }
  if (L2_vec)
  {
    OPENSSL_cleanse(L2_vec, rounds * sizeof(secp256k1_pubkey));
    free(L2_vec);
  }
  if (R1_vec)
  {
    OPENSSL_cleanse(R1_vec, rounds * sizeof(secp256k1_pubkey));
    free(R1_vec);
  }
  if (R2_vec)
  {
    OPENSSL_cleanse(R2_vec, rounds * sizeof(secp256k1_pubkey));
    free(R2_vec);
  }

  if (y_powers)
  {
    OPENSSL_cleanse(y_powers, n * kMPT_SCALAR_SIZE);
    free(y_powers);
  }
  if (z_j2)
  {
    OPENSSL_cleanse(z_j2, m * kMPT_SCALAR_SIZE);
    free(z_j2);
  }

  return ok;
}
/**
 * Verifies an aggregated Bulletproof range proof for m commitments.
 *
 * Checks that the values committed in `commitment_C_vec` are all within the
 * [0, 2^64) range.
 *
 * Usage Notes:
 * - The generator vectors G_vec and H_vec must have length n = 64 * m.
 * - The commitment array `commitment_C_vec` must contain m elements.
 * (For a single proof where m=1, pass a pointer to the single commitment).
 * - To bind commitments to the proof transcript, include them in the
 * `context_id` hash before calling this function.
 *
 * Serialized Proof Format:
 * - A, S, T1, T2       (4 * 33 bytes)
 * - L1,L2,R1,R2       (4 * rounds * 33 bytes, round-major)
 * - a, b               (2 * 32 bytes)
 * - t_hat, tau_x, mu   (3 * 32 bytes)
 *
 * Total Size: 292 + (132 * rounds) bytes, where
 * rounds is the number of dynamic-padding 3W reductions to length 1.
 *
 * Returns 1 if valid, 0 otherwise.
 */

int secp256k1_bulletproof_verify_agg(
    const secp256k1_context *ctx,
    const secp256k1_pubkey *G_vec, /* length n = 64*m */
    const secp256k1_pubkey *H_vec, /* length n = 64*m */
    const unsigned char *proof, size_t proof_len,
    const secp256k1_pubkey *commitment_C_vec, /* length m */
    size_t m, const secp256k1_pubkey *h_generator,
    const unsigned char *context_id)
{
  if (!ctx || !G_vec || !H_vec || !proof || !commitment_C_vec || !h_generator)
    return 0;
  if (m == 0 || m > BP_MAX_VALUES)
    return 0;
  /* Aggregation requires n = 64*m to be power-of-two => m must be power-of-two.
   */
  if ((m & (m - 1)) != 0)
    return 0;

  const size_t n = BP_TOTAL_BITS(m); /* 64*m */
  const size_t rounds = bp_ipa_rounds_3w(n);

  /* Proof length is dynamic in aggregated mode */
  const size_t expected_len = 292 + 132 * rounds;
  if (proof_len != expected_len)
    return 0;

  /* --- Unpack proof --- */
  secp256k1_pubkey A, S, T1, T2;
  secp256k1_pubkey U;

  secp256k1_pubkey *L1_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *L2_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *R1_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));
  secp256k1_pubkey *R2_vec =
      (secp256k1_pubkey *)malloc(rounds * sizeof(secp256k1_pubkey));
  if (!L1_vec || !L2_vec || !R1_vec || !R2_vec)
  {
    free(L1_vec);
    free(L2_vec);
    free(R1_vec);
    free(R2_vec);
    return 0;
  }

  /* Heap allocations whose lifetime spans multiple goto-fail sites.
   * Declared here, ahead of the first `goto fail`, and NULL-initialized so the
   * centralized free at the `fail:` label is a no-op when execution exits
   * before the actual malloc. */
  unsigned char *y_powers = NULL;
  unsigned char *y_inv_powers = NULL;
  unsigned char (*y_block_sum)[kMPT_SCALAR_SIZE] = NULL;

  unsigned char a_final[kMPT_SCALAR_SIZE], b_final[kMPT_SCALAR_SIZE];
  unsigned char t_hat[kMPT_SCALAR_SIZE], tau_x[kMPT_SCALAR_SIZE],
      mu[kMPT_SCALAR_SIZE];

  unsigned char y[kMPT_SCALAR_SIZE], z[kMPT_SCALAR_SIZE], x[kMPT_SCALAR_SIZE];
  unsigned char ux_scalar[kMPT_SCALAR_SIZE];
  unsigned char z_sq[kMPT_SCALAR_SIZE];

  const unsigned char *ptr = proof;

  if (!secp256k1_ec_pubkey_parse(ctx, &A, ptr, kMPT_PUBKEY_SIZE))
    goto fail;
  ptr += kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_parse(ctx, &S, ptr, kMPT_PUBKEY_SIZE))
    goto fail;
  ptr += kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_parse(ctx, &T1, ptr, kMPT_PUBKEY_SIZE))
    goto fail;
  ptr += kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_parse(ctx, &T2, ptr, kMPT_PUBKEY_SIZE))
    goto fail;
  ptr += kMPT_PUBKEY_SIZE;

  for (size_t i = 0; i < rounds; i++)
  {
    if (!secp256k1_ec_pubkey_parse(ctx, &L1_vec[i], ptr, kMPT_PUBKEY_SIZE))
      goto fail;
    ptr += kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_parse(ctx, &L2_vec[i], ptr, kMPT_PUBKEY_SIZE))
      goto fail;
    ptr += kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_parse(ctx, &R1_vec[i], ptr, kMPT_PUBKEY_SIZE))
      goto fail;
    ptr += kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_parse(ctx, &R2_vec[i], ptr, kMPT_PUBKEY_SIZE))
      goto fail;
    ptr += kMPT_PUBKEY_SIZE;
  }

  memcpy(a_final, ptr, kMPT_SCALAR_SIZE);
  ptr += kMPT_SCALAR_SIZE;
  memcpy(b_final, ptr, kMPT_SCALAR_SIZE);
  ptr += kMPT_SCALAR_SIZE;
  memcpy(t_hat, ptr, kMPT_SCALAR_SIZE);
  ptr += kMPT_SCALAR_SIZE;
  memcpy(tau_x, ptr, kMPT_SCALAR_SIZE);
  ptr += kMPT_SCALAR_SIZE;
  memcpy(mu, ptr, kMPT_SCALAR_SIZE);
  ptr += kMPT_SCALAR_SIZE;

  /* Proof scalars must be canonical field elements; zero is allowed. */
  if (!scalar_is_canonical_3w(a_final) || !scalar_is_canonical_3w(b_final) ||
      !scalar_is_canonical_3w(t_hat) || !scalar_is_canonical_3w(tau_x) ||
      !scalar_is_canonical_3w(mu))
    goto fail;

  /* Derive U */
  {
    secp256k1_pubkey U_arr[1];
    if (!secp256k1_mpt_get_generator_vector(ctx, U_arr, 1,
                                            (const unsigned char *)"BP_U", 4))
      goto fail;
    U = U_arr[0];
  }

  /* --- Fiat–Shamir: y,z,x ---
   *
   * T_0 = domain || gens_digest || N (BE u32) || m (BE u32) || C_0..C_{m-1}
   * T_1 = T_0 || A || S
   *   y = H(T_1 || context_id)
   *   z = H(T_1 || y || context_id)
   *
   * MUST agree byte-for-byte with the prover; see the matching block in
   * secp256k1_bulletproof_prove_agg.
   */
  unsigned char A_ser[kMPT_PUBKEY_SIZE], S_ser[kMPT_PUBKEY_SIZE],
      T1_ser[kMPT_PUBKEY_SIZE], T2_ser[kMPT_PUBKEY_SIZE];
  unsigned char gens_digest[kMPT_HALF_SHA_SIZE];
  unsigned char N_be[4], m_be[4];
  size_t slen;
  EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
  int fs_ok = 0;

  if (!mdctx)
    goto fail;

  if (!bulletproof_gens_digest(ctx, h_generator, G_vec, H_vec, n, gens_digest))
    goto fs_fail;
  bulletproof_be32_encode(N_be, (uint32_t)BP_VALUE_BITS);
  bulletproof_be32_encode(m_be, (uint32_t)m);

  /* Serialize A,S,T1,T2 */
  slen = kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_serialize(ctx, A_ser, &slen, &A,
                                     SECP256K1_EC_COMPRESSED) ||
      slen != kMPT_PUBKEY_SIZE)
    goto fs_fail;
  slen = kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_serialize(ctx, S_ser, &slen, &S,
                                     SECP256K1_EC_COMPRESSED) ||
      slen != kMPT_PUBKEY_SIZE)
    goto fs_fail;
  slen = kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_serialize(ctx, T1_ser, &slen, &T1,
                                     SECP256K1_EC_COMPRESSED) ||
      slen != kMPT_PUBKEY_SIZE)
    goto fs_fail;
  slen = kMPT_PUBKEY_SIZE;
  if (!secp256k1_ec_pubkey_serialize(ctx, T2_ser, &slen, &T2,
                                     SECP256K1_EC_COMPRESSED) ||
      slen != kMPT_PUBKEY_SIZE)
    goto fs_fail;

  /* ---------------- y = H(domain || gens || N || m || C_i || A || S ||
   * context) ---------------- */
  if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, "MPT_BULLETPROOF_RANGE", 21) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, gens_digest, 32) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, N_be, 4) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, m_be, 4) != 1)
    goto fs_fail;

  for (size_t i = 0; i < m; i++)
  {
    unsigned char C_ser[kMPT_PUBKEY_SIZE];
    size_t c_len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, C_ser, &c_len, &commitment_C_vec[i],
                                       SECP256K1_EC_COMPRESSED) ||
        c_len != kMPT_PUBKEY_SIZE)
      goto fs_fail;
    if (EVP_DigestUpdate(mdctx, C_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_fail;
  }

  if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (context_id && EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestFinal_ex(mdctx, y, NULL) != 1)
    goto fs_fail;

  secp256k1_mpt_scalar_reduce32(y, y);

  /* ---------------- z = H(domain || gens || N || m || C_i || A || S || y ||
   * context) ---------------- */
  if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, "MPT_BULLETPROOF_RANGE", 21) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, gens_digest, 32) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, N_be, 4) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, m_be, 4) != 1)
    goto fs_fail;

  for (size_t i = 0; i < m; i++)
  {
    unsigned char C_ser[kMPT_PUBKEY_SIZE];
    size_t c_len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, C_ser, &c_len, &commitment_C_vec[i],
                                       SECP256K1_EC_COMPRESSED) ||
        c_len != kMPT_PUBKEY_SIZE)
      goto fs_fail;
    if (EVP_DigestUpdate(mdctx, C_ser, kMPT_PUBKEY_SIZE) != 1)
      goto fs_fail;
  }

  if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, y, kMPT_SCALAR_SIZE) != 1)
    goto fs_fail;
  if (context_id && EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestFinal_ex(mdctx, z, NULL) != 1)
    goto fs_fail;

  secp256k1_mpt_scalar_reduce32(z, z);

  if (!secp256k1_ec_seckey_verify(ctx, y) ||
      !secp256k1_ec_seckey_verify(ctx, z))
    goto fs_fail;

  /* Powers */
  y_powers = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  y_inv_powers = (unsigned char *)malloc(n * kMPT_SCALAR_SIZE);
  if (!y_powers || !y_inv_powers)
    goto fs_fail;

  unsigned char y_inv[kMPT_SCALAR_SIZE];
  scalar_vector_powers(ctx, (unsigned char (*)[kMPT_SCALAR_SIZE])y_powers, y,
                       n);
  secp256k1_mpt_scalar_inverse(y_inv, y);
  scalar_vector_powers(ctx, (unsigned char (*)[kMPT_SCALAR_SIZE])y_inv_powers,
                       y_inv, n);

  /* ---------------- x = H(A || S || y || z || T1 || T2 || context)
   * ---------------- */
  if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, y, kMPT_SCALAR_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, z, kMPT_SCALAR_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, T1_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestUpdate(mdctx, T2_ser, kMPT_PUBKEY_SIZE) != 1)
    goto fs_fail;
  if (context_id && EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
    goto fs_fail;
  if (EVP_DigestFinal_ex(mdctx, x, NULL) != 1)
    goto fs_fail;

  secp256k1_mpt_scalar_reduce32(x, x);

  if (!secp256k1_ec_seckey_verify(ctx, x))
    goto fs_fail;

  fs_ok = 1;

fs_fail:
  EVP_MD_CTX_free(mdctx);
  if (!fs_ok)
    goto fail;

  /* z^2 */
  secp256k1_mpt_scalar_mul(z_sq, z, z);

  /* =========================================================================
   * Step 3: Verify polynomial identity:
   *   t_hat*G + tau_x*H == (sum_j z^(j+2) * V_j) + delta(y,z)*G + x*T1 + x^2*T2
   * =========================================================================
   */

  /* --- delta(y,z) for aggregation --- */
  y_block_sum =
      (unsigned char (*)[kMPT_SCALAR_SIZE])malloc(m * kMPT_SCALAR_SIZE);
  if (!y_block_sum)
    goto fail;

  unsigned char two_sum[kMPT_SCALAR_SIZE];
  compute_delta_scalars(ctx, y_block_sum, two_sum, y, m);

  unsigned char delta[kMPT_SCALAR_SIZE] = {0};
  unsigned char sum_y_all[kMPT_SCALAR_SIZE] = {0};

  /* sum_y_all = sum_{k=0}^{n-1} y^k = sum_j y_block_sum[j] */
  for (size_t j = 0; j < m; j++)
  {
    secp256k1_mpt_scalar_add(sum_y_all, sum_y_all, y_block_sum[j]);
  }

  /* delta += (z - z^2) * sum_y_all */
  {
    unsigned char z_minus_z2[kMPT_SCALAR_SIZE], tmp[kMPT_SCALAR_SIZE];
    secp256k1_mpt_scalar_sub(z_minus_z2, z, z_sq);
    secp256k1_mpt_scalar_mul(tmp, z_minus_z2, sum_y_all);
    secp256k1_mpt_scalar_add(delta, delta, tmp);
    OPENSSL_cleanse(z_minus_z2, kMPT_SCALAR_SIZE);
    OPENSSL_cleanse(tmp, kMPT_SCALAR_SIZE);
  }

  /* delta -= sum_{j=0}^{m-1} z^(j+3) * two_sum */
  for (size_t j = 0; j < m; j++)
  {
    unsigned char z_j3[kMPT_SCALAR_SIZE], tmp[kMPT_SCALAR_SIZE];
    scalar_pow_u32(ctx, z_j3, z, (unsigned int)(j + 3));
    secp256k1_mpt_scalar_mul(tmp, z_j3, two_sum);
    secp256k1_mpt_scalar_negate(tmp, tmp);
    secp256k1_mpt_scalar_add(delta, delta, tmp);
    OPENSSL_cleanse(z_j3, kMPT_SCALAR_SIZE);
    OPENSSL_cleanse(tmp, kMPT_SCALAR_SIZE);
  }

  OPENSSL_cleanse(sum_y_all, kMPT_SCALAR_SIZE);

  /* LHS = t_hat*G + tau_x*Base */
  secp256k1_pubkey LHS;
  {
    unsigned char zero32[kMPT_SCALAR_SIZE] = {0};
    int have_t = 0, have_tau = 0;
    secp256k1_pubkey tG, tauH;

    if (memcmp(t_hat, zero32, kMPT_SCALAR_SIZE) != 0)
    {
      if (!secp256k1_ec_pubkey_create(ctx, &tG, t_hat))
      {
        goto fail;
      }
      have_t = 1;
    }
    if (memcmp(tau_x, zero32, kMPT_SCALAR_SIZE) != 0)
    {
      tauH = *h_generator;
      if (!mpt_ct_pubkey_tweak_mul(ctx, &tauH, tau_x))
      {
        goto fail;
      }
      have_tau = 1;
    }
    if (have_t && have_tau)
    {
      const secp256k1_pubkey *pts[2] = {&tG, &tauH};
      if (!secp256k1_ec_pubkey_combine(ctx, &LHS, pts, 2))
      {
        goto fail;
      }
    }
    else if (have_t)
    {
      LHS = tG;
    }
    else if (have_tau)
    {
      LHS = tauH;
    }
    else
    {
      goto fail;
    }
  }

  /* RHS = (sum_j z^(j+2) V_j) + delta*G + x*T1 + x^2*T2 */
  secp256k1_pubkey RHS;
  {
    secp256k1_pubkey acc, tmpP;
    int inited = 0;
    unsigned char zero32[kMPT_SCALAR_SIZE] = {0};

    /* sum_j z^(j+2) V_j */
    for (size_t j = 0; j < m; j++)
    {
      unsigned char z_j2[kMPT_SCALAR_SIZE];
      scalar_pow_u32(ctx, z_j2, z, (unsigned int)(j + 2));

      if (memcmp(z_j2, zero32, kMPT_SCALAR_SIZE) != 0)
      {
        tmpP = commitment_C_vec[j];
        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmpP, z_j2))
        {
          goto fail;
        }
        if (!add_term(ctx, &acc, &inited, &tmpP))
        {
          goto fail;
        }
      }
      OPENSSL_cleanse(z_j2, kMPT_SCALAR_SIZE);
    }

    /* + delta*G */
    if (!scalar_is_zero(delta))
    {
      secp256k1_pubkey deltaG;
      if (!secp256k1_ec_pubkey_create(ctx, &deltaG, delta))
        goto fail;
      if (!add_term(ctx, &acc, &inited, &deltaG))
        goto fail;
    }

    /* + x*T1 */
    if (memcmp(x, zero32, kMPT_SCALAR_SIZE) != 0)
    {
      tmpP = T1;
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmpP, x))
      {
        goto fail;
      }
      if (!add_term(ctx, &acc, &inited, &tmpP))
      {
        goto fail;
      }
    }

    /* + x^2*T2 */
    unsigned char x_sq[kMPT_SCALAR_SIZE];
    secp256k1_mpt_scalar_mul(x_sq, x, x);
    if (memcmp(x_sq, zero32, kMPT_SCALAR_SIZE) != 0)
    {
      tmpP = T2;
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &tmpP, x_sq))
      {
        OPENSSL_cleanse(x_sq, kMPT_SCALAR_SIZE);
        goto fail;
      }
      if (!add_term(ctx, &acc, &inited, &tmpP))
      {
        OPENSSL_cleanse(x_sq, kMPT_SCALAR_SIZE);
        goto fail;
      }
    }
    OPENSSL_cleanse(x_sq, kMPT_SCALAR_SIZE);

    if (!inited)
    {
      goto fail;
    }
    RHS = acc;
  }

  if (!pubkey_equal(ctx, &LHS, &RHS))
  {
    goto fail;
  }

  /* =========================================================================
   * Step 4: Build P and Verify IPA
   * =========================================================================
   */

  unsigned char ipa_transcript_id[kMPT_SCALAR_SIZE];
  {
    unsigned char A_ser[kMPT_PUBKEY_SIZE], S_ser[kMPT_PUBKEY_SIZE],
        T1_ser[kMPT_PUBKEY_SIZE], T2_ser[kMPT_PUBKEY_SIZE];
    size_t len;
    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    int ok = 0;
    unsigned int md_len = 0;

    if (!mdctx)
      goto fail;

    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, A_ser, &len, &A,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto ipa_tid_cleanup;
    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, S_ser, &len, &S,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto ipa_tid_cleanup;
    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, T1_ser, &len, &T1,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto ipa_tid_cleanup;
    len = kMPT_PUBKEY_SIZE;
    if (!secp256k1_ec_pubkey_serialize(ctx, T2_ser, &len, &T2,
                                       SECP256K1_EC_COMPRESSED) ||
        len != kMPT_PUBKEY_SIZE)
      goto ipa_tid_cleanup;

    if (EVP_DigestInit_ex(mdctx, EVP_sha256(), NULL) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, "MPT_BP_IPA_3W", 13) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, A_ser, kMPT_PUBKEY_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, S_ser, kMPT_PUBKEY_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, T1_ser, kMPT_PUBKEY_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, T2_ser, kMPT_PUBKEY_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, y, kMPT_SCALAR_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, z, kMPT_SCALAR_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, x, kMPT_SCALAR_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestUpdate(mdctx, t_hat, kMPT_SCALAR_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (context_id &&
        EVP_DigestUpdate(mdctx, context_id, kMPT_SCALAR_SIZE) != 1)
      goto ipa_tid_cleanup;
    if (EVP_DigestFinal_ex(mdctx, ipa_transcript_id, &md_len) != 1)
      goto ipa_tid_cleanup;
    if (md_len != kMPT_HALF_SHA_SIZE)
      goto ipa_tid_cleanup;

    ok = 1;

  ipa_tid_cleanup:
    EVP_MD_CTX_free(mdctx);
    if (!ok)
      goto fail;
  }

  if (!derive_ipa_binding_challenge(ctx, ux_scalar, ipa_transcript_id, t_hat))
    goto fail;

  secp256k1_pubkey P = A;

  /* P += x*S */
  {
    secp256k1_pubkey xS = S;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &xS, x))
    {
      goto fail;
    }

    secp256k1_pubkey newP;
    const secp256k1_pubkey *pts[2] = {&P, &xS};
    if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts, 2))
      goto fail;
    P = newP;
  }

  /* P += sum_{k=0}^{n-1} [ (-z)*G_k + ( z*y^k + z^(block+2)*z^2*2^i ) *
   * (y^{-k}*H_k) ] */
  unsigned char neg_z[kMPT_SCALAR_SIZE];
  secp256k1_mpt_scalar_negate(neg_z, z);

  for (size_t j = 0; j < m; j++)
  {
    unsigned char z_j2[kMPT_SCALAR_SIZE];
    scalar_pow_u32(ctx, z_j2, z, (unsigned int)(j + 2));

    for (size_t i = 0; i < 64; i++)
    {
      const size_t k = j * 64 + i;

      /* ---- Gi term: (-z) * G_k ---- */
      if (!scalar_is_zero(neg_z))
      {
        secp256k1_pubkey Gi = G_vec[k];
        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &Gi, neg_z))
          goto fail;

        secp256k1_pubkey newP;
        const secp256k1_pubkey *pts2[2] = {&P, &Gi};
        if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts2, 2))
          goto fail;
        P = newP;
      }

      /* ---- Hi term: termH * (y^{-k} * H_k) ---- */
      unsigned char termH[kMPT_SCALAR_SIZE], tmp[kMPT_SCALAR_SIZE];
      unsigned char two_i[kMPT_SCALAR_SIZE] = {0};

      secp256k1_mpt_scalar_mul(
          termH, z, (const unsigned char *)(y_powers + kMPT_SCALAR_SIZE * k));

      two_i[31 - (i / 8)] = (unsigned char)(1u << (i % 8));
      secp256k1_mpt_scalar_mul(tmp, z_j2, two_i);
      secp256k1_mpt_scalar_add(termH, termH, tmp);

      if (!scalar_is_zero(termH))
      {
        secp256k1_pubkey Hi = H_vec[k];

        /* Hi = (y^{-k} * H_k) */
        if (!secp256k1_ec_pubkey_tweak_mul(
                ctx, &Hi,
                (const unsigned char *)(y_inv_powers + kMPT_SCALAR_SIZE * k)))
          goto fail;

        /* Hi = termH * Hi */
        if (!secp256k1_ec_pubkey_tweak_mul(ctx, &Hi, termH))
          goto fail;

        secp256k1_pubkey newP;
        const secp256k1_pubkey *pts2[2] = {&P, &Hi};
        if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts2, 2))
          goto fail;
        P = newP;
      }

      OPENSSL_cleanse(tmp, kMPT_SCALAR_SIZE);
      OPENSSL_cleanse(termH, kMPT_SCALAR_SIZE);
    }

    OPENSSL_cleanse(z_j2, kMPT_SCALAR_SIZE);
  }

  /* P += (t_hat * ux) * U */
  {
    unsigned char t_hat_ux[kMPT_SCALAR_SIZE];
    unsigned char zero32[kMPT_SCALAR_SIZE] = {0};
    secp256k1_mpt_scalar_mul(t_hat_ux, t_hat, ux_scalar);

    if (memcmp(t_hat_ux, zero32, kMPT_SCALAR_SIZE) != 0)
    {
      secp256k1_pubkey Q = U;
      if (!secp256k1_ec_pubkey_tweak_mul(ctx, &Q, t_hat_ux))
      {
        OPENSSL_cleanse(t_hat_ux, kMPT_SCALAR_SIZE);
        goto fail;
      }
      const secp256k1_pubkey *pts2[2] = {&P, &Q};
      secp256k1_pubkey newP;
      if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts2, 2))
        goto fail;
      P = newP;
    }
    OPENSSL_cleanse(t_hat_ux, kMPT_SCALAR_SIZE);
  }

  /* P -= mu*h_generator */
  {
    unsigned char neg_mu[kMPT_SCALAR_SIZE];
    secp256k1_mpt_scalar_negate(neg_mu, mu);

    secp256k1_pubkey mu_term = *h_generator;
    if (!secp256k1_ec_pubkey_tweak_mul(ctx, &mu_term, neg_mu))
    {
      OPENSSL_cleanse(neg_mu, kMPT_SCALAR_SIZE);
      goto fail;
    }
    OPENSSL_cleanse(neg_mu, kMPT_SCALAR_SIZE);

    const secp256k1_pubkey *pts2[2] = {&P, &mu_term};
    secp256k1_pubkey newP;
    if (!secp256k1_ec_pubkey_combine(ctx, &newP, pts2, 2))
      goto fail;
    P = newP;
  }

  /* Build Hprime = y^{-k} * H_k (length n) */
  secp256k1_pubkey *Hprime =
      (secp256k1_pubkey *)malloc(n * sizeof(secp256k1_pubkey));
  if (!Hprime)
  {
    goto fail;
  }

  for (size_t k = 0; k < n; k++)
  {
    Hprime[k] = H_vec[k];
    if (!secp256k1_ec_pubkey_tweak_mul(
            ctx, &Hprime[k],
            (const unsigned char *)(y_inv_powers + kMPT_SCALAR_SIZE * k)))
    {
      free(Hprime);
      goto fail;
    }
  }
  /* IPA verify */

  int ok = ipa_verify_explicit_3w(
      ctx, G_vec, Hprime, &U, &P, L1_vec, L2_vec, R1_vec, R2_vec, n,
      a_final, b_final, ux_scalar, ipa_transcript_id);

  free(Hprime);
  free(y_block_sum);
  free(y_powers);
  free(y_inv_powers);
  free(L1_vec);
  free(L2_vec);
  free(R1_vec);
  free(R2_vec);

  return ok ? 1 : 0;

fail:
  /* Centralized cleanup. All goto-fail sites land here; pointers that have
   * not yet been allocated are still NULL, and free(NULL) is a no-op. */
  free(y_block_sum);
  free(y_powers);
  free(y_inv_powers);
  free(L1_vec);
  free(L2_vec);
  free(R1_vec);
  free(R2_vec);
  return 0;
}