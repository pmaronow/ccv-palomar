module

public import Mathlib


@[expose] public section

/-! Finite multilevel L² aggregation with geometric weights. These facts
allow all levels to use the same observations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 500000

theorem secondMoment_sum_le_weighted {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ℝ)
    (hE : ∀ i, (∫ z, X i z ^ 2 ∂μ) ≤ B * w i ^ 2) :
    (∫ z, (∑ i, X i z) ^ 2 ∂μ) ≤ B * (∑ i, w i) ^ 2 := by
  classical
  have hsum : MemLp (fun z => ∑ i, X i z) 2 μ := memLp_finsetSum _ (fun i _ => hX i)
  have hi (i) : Integrable (fun z => X i z ^ 2 / w i) μ :=
    (hX i).integrable_sq.div_const _
  have hpoint (z) : (∑ i, X i z) ^ 2 ≤ (∑ i, w i) * ∑ i, X i z ^ 2 / w i := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => (hw i).le) (fun i _ => div_nonneg (sq_nonneg _) (hw i).le)
    intro i _
    exact le_of_eq (by field_simp [(hw i).ne'])
  have hm := integral_mono hsum.integrable_sq
    ((integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul (∑ i, w i)) hpoint
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i)] at hm
  have hterms : (∑ i, ∫ z, X i z ^ 2 / w i ∂μ) ≤ B * ∑ i, w i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [integral_div]
    apply (div_le_div_of_nonneg_right (hE i) (hw i).le).trans_eq
    field_simp [(hw i).ne']
  calc
    _ ≤ (∑ i, w i) * (B * ∑ i, w i) := hm.trans
      (mul_le_mul_of_nonneg_left hterms (Finset.sum_nonneg (fun i _ => (hw i).le)))
    _ = _ := by ring

theorem dyadic_geometric_sum_bound (J : ℕ) :
    (∑ j : Fin (J + 1), (2 : ℝ) ^ j.val) ≤ 2 * (2 : ℝ) ^ J := by
  rw [Fin.sum_univ_eq_sum_range]
  have h := geom_sum_mul_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (J + 1)
  norm_num only [sub_self, add_zero, sub_zero, mul_one] at h
  rw [h, pow_succ]
  linarith

theorem secondMoment_dyadic_sum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (J : ℕ) (X : Fin (J + 1) → Ω → ℝ)
    (hX : ∀ j, MemLp (X j) 2 μ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ j, (∫ z, X j z ^ 2 ∂μ) ≤ B * ((2 : ℝ) ^ j.val) ^ 2) :
    (∫ z, (∑ j, X j z) ^ 2 ∂μ) ≤ 4 * B * ((2 : ℝ) ^ J) ^ 2 := by
  have h := secondMoment_sum_le_weighted μ X hX (fun j => (2 : ℝ) ^ j.val)
    (fun _ => by positivity) B hE
  have hs := dyadic_geometric_sum_bound J
  have hnon : 0 ≤ ∑ j : Fin (J + 1), (2 : ℝ) ^ j.val := by positivity
  apply h.trans
  nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hs 2) hB]

end NearlyMinimax
