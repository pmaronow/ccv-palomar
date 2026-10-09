module

public import NearlyMinimax.FactorialSeriesTail
public import Mathlib.Analysis.SpecificLimits.Basic


@[expose] public section

/-! Finite geometric summation of the actual higher-target row activity bounds.
The estimate preserves the leading exp(tau_M * M) activity factor. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

theorem finite_geometric_tail_le_two_mul {q : ℝ} (hq : 0 ≤ q) (hqh : q ≤ 1 / 2)
    (m : ℕ) : (∑ j ∈ Finset.range m, q ^ (j + 1)) ≤ 2 * q := by
  calc
    _ = q * ∑ j ∈ Finset.range m, q ^ j := by simp_rw [pow_succ]; rw [Finset.mul_sum]; ring
    _ ≤ q * ∑ j ∈ Finset.range m, (1 / (2 : ℝ)) ^ j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hq hqh j) hq
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le m) hq
    _ = _ := mul_comm _ _

theorem finite_activity_tail_le {K q : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hqh : q ≤ 1 / 2) (m : ℕ) (B : ℕ → ℝ)
    (hB : ∀ j ∈ Finset.range m, B j ≤ K * q ^ (j + 1)) :
    (∑ j ∈ Finset.range m, B j) ≤ 2 * K * q := by
  calc
    _ ≤ ∑ j ∈ Finset.range m, K * q ^ (j + 1) := Finset.sum_le_sum hB
    _ = K * ∑ j ∈ Finset.range m, q ^ (j + 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (2 * q) := mul_le_mul_of_nonneg_left (finite_geometric_tail_le_two_mul hq hqh m) hK
    _ = _ := by ring

/-- Both families can have any finite number of targets. The small activity
ratios remove the D² factor without an additional exponential in M. -/
theorem higher_band_activity_sum_le {K D N ell EM ED q1 q2 : ℝ}
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hEM : 1 ≤ EM) (hED : 0 ≤ ED)
    (hell : 0 ≤ ell) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hq1h : q1 ≤ 1 / 2) (hq21 : q2 ≤ q1)
    (hsmall : D ^ 2 * q1 ≤ 1) (hcoarse : ED * ell ≤ N)
    (mc mf : ℕ) (Bc Bf : ℕ → ℝ)
    (hBc : ∀ j ∈ Finset.range mc, Bc j ≤ K * D ^ 2 * ED * N * ell * q1 ^ (j + 1))
    (hBf : ∀ j ∈ Finset.range mf, Bf j ≤ K * D ^ 2 * EM * N ^ 2 * q2 ^ (j + 1)) :
    (∑ j ∈ Finset.range mc, Bc j) + (∑ j ∈ Finset.range mf, Bf j) ≤
      4 * K * N ^ 2 * EM := by
  have hEM0 : 0 ≤ EM := (by norm_num : (0 : ℝ) ≤ 1).trans hEM
  have hc := finite_activity_tail_le (by positivity : 0 ≤ K * D ^ 2 * ED * N * ell)
    hq1 hq1h mc Bc hBc
  have hf := finite_activity_tail_le (by positivity : 0 ≤ K * D ^ 2 * EM * N ^ 2)
    hq2 (hq21.trans hq1h) mf Bf hBf
  have hsmall2 : D ^ 2 * q2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hq21 (sq_nonneg D)).trans hsmall
  have hc' : (∑ j ∈ Finset.range mc, Bc j) ≤ 2 * K * N ^ 2 := by
    apply hc.trans
    calc
      _ = 2 * K * N * (ED * ell) * (D ^ 2 * q1) := by ring
      _ ≤ 2 * K * N * N * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoarse (by positivity)) hsmall
          (mul_nonneg (sq_nonneg D) hq1) (by positivity)
      _ = _ := by ring
  have hf' : (∑ j ∈ Finset.range mf, Bf j) ≤ 2 * K * N ^ 2 * EM := by
    apply hf.trans
    calc
      _ = (2 * K * N ^ 2 * EM) * (D ^ 2 * q2) := by ring
      _ ≤ (2 * K * N ^ 2 * EM) * 1 := mul_le_mul_of_nonneg_left hsmall2 (by positivity)
      _ = _ := mul_one _
  have hem := mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 2 * K * N ^ 2)
  nlinarith only [hc', hf', hem]

end NearlyMinimax
