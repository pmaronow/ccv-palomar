module

public import NearlyMinimax.LowSmoothnessGridChoice


@[expose] public section

/-!
# Optimization of the actual elementary pair grid

This deterministic module optimizes the finite-grid mean-square envelope
`1/n + k^d/(n(n-1)) + k^(-4 rho)` for the actual natural ceiling grid.
The estimator inequality is an explicit input to the final scalar corollary.
-/

noncomputable section
namespace NearlyMinimax

def pairGridMSEEnvelope (d : ℕ) (s x : ℝ) : ℝ :=
  1 / x + (lowSmoothnessGrid d s x : ℝ) ^ d / (x * (x - 1)) +
    (lowSmoothnessGrid d s x : ℝ) ^ (-4 * s)

theorem pairGrid_denominator_bound {x : ℝ} (hx : 2 ≤ x) :
    x ^ 2 / 2 ≤ x * (x - 1) := by nlinarith

theorem pairGridMSEEnvelope_bound {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 2 ≤ x) :
    pairGridMSEEnvelope d s x ≤
      (2 * (5 : ℝ) ^ d + 1) * (1 / x + x ^ (-8 * s / ((d : ℝ) + 4 * s))) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hden : 0 < x * (x - 1) := mul_pos hx0 (by linarith)
  have hp : 0 ≤ (lowSmoothnessGrid d s x : ℝ) ^ d := by positivity
  have hfirst : (lowSmoothnessGrid d s x : ℝ) ^ d / (x * (x - 1)) ≤
      2 * ((lowSmoothnessGrid d s x : ℝ) ^ d / x ^ 2) := by
    have hh := div_le_div_of_nonneg_left hp (show 0 < x ^ 2 / 2 by positivity)
      (pairGrid_denominator_bound hx)
    have hid : (lowSmoothnessGrid d s x : ℝ) ^ d / (x ^ 2 / 2) =
        2 * ((lowSmoothnessGrid d s x : ℝ) ^ d / x ^ 2) := by ring
    exact hh.trans_eq hid
  have hvar := mul_le_mul_of_nonneg_left (lowSmoothnessGrid_pair_variance_budget (d := d) hs hx1)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hbias := lowSmoothnessGrid_pair_bias_budget (d := d) hs hx1
  have hcoef : 0 ≤ 2 * (5 : ℝ) ^ d * (1 / x) := by positivity
  unfold pairGridMSEEnvelope
  nlinarith only [hfirst, hvar, hbias, hcoef]

theorem sqrt_inverse_sample {x : ℝ} (hx : 0 < x) :
    Real.sqrt (1 / x) = x ^ (-(1 / 2 : ℝ)) := by
  rw [one_div, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg hx.le]

theorem sqrt_pair_rate {d : ℕ} {s x : ℝ} (hx : 0 < x) :
    Real.sqrt (x ^ (-8 * s / ((d : ℝ) + 4 * s))) = x ^ (-4 * s / ((d : ℝ) + 4 * s)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- Applying the concrete finite-grid MSE bound gives the elementary root-mean-square rate. -/
theorem pairGrid_rms_of_mse_bound {d : ℕ} {s x C R : ℝ}
    (hs : 0 < s) (hx : 2 ≤ x) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRisk : R ^ 2 ≤ C * pairGridMSEEnvelope d s x) :
    R ≤ Real.sqrt (C * (2 * (5 : ℝ) ^ d + 1)) *
      (x ^ (-(1 / 2 : ℝ)) + x ^ (-4 * s / ((d : ℝ) + 4 * s))) := by
  have hx0 : 0 < x := by linarith
  have henv := mul_le_mul_of_nonneg_left (pairGridMSEEnvelope_bound (d := d) hs hx) hC
  have hsq := Real.sqrt_le_sqrt (hRisk.trans henv)
  rw [Real.sqrt_sq hR, ← mul_assoc, Real.sqrt_mul (by positivity)] at hsq
  apply hsq.trans
  have hadd : Real.sqrt (1 / x + x ^ (-8 * s / ((d : ℝ) + 4 * s))) ≤
      Real.sqrt (1 / x) + Real.sqrt (x ^ (-8 * s / ((d : ℝ) + 4 * s))) := by
    have hA : 0 ≤ 1 / x := by positivity
    have hB : 0 ≤ x ^ (-8 * s / ((d : ℝ) + 4 * s)) := (Real.rpow_pos_of_pos hx0 _).le
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg (1 / x)) (Real.sqrt_nonneg (x ^ (-8 * s / ((d : ℝ) + 4 * s))))]
  rw [sqrt_inverse_sample hx0, sqrt_pair_rate hx0] at hadd
  exact mul_le_mul_of_nonneg_left hadd (Real.sqrt_nonneg _)

end NearlyMinimax
