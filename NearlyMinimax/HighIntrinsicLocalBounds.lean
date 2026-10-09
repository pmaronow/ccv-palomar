module

public import NearlyMinimax.HighIntrinsicPeriodizedBounds
public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! Literal intrinsic coefficient-ball bounds for the actual local regression
field with one coefficient block removed. Zeroing that block gives exactly
the whole periodic field, so no extra window amplitude is introduced. -/
noncomputable section
open Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 60000
attribute [local instance] Classical.propDecidable

/-- The original coefficient state with exactly one block set to zero. -/
def highCoefficientWithout {d k D : ℕ}
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) : HighWindowLabels d k → HighFrameIndex d D → ℝ :=
  fun l γ => if l = j then 0 else c l γ

theorem highLocalFieldWithout_eq_zero_block (d k D : ℕ) [NeZero k]
    (η : ℝ) (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (x : Covariate d) :
    highLocalFieldWithout d k D η c j x =
      highFrameField d k η (fun l => highFramePolynomial (highCoefficientWithout c j l)) x := by
  unfold highLocalFieldWithout highFrameField
  apply congrArg (fun t : ℝ => η*t)
  rw [← Finset.sum_erase_add (Finset.univ : Finset (HighWindowLabels d k))
    (fun l => highPeriodizedChart d k l
      (highFrameProfile (highFramePolynomial (highCoefficientWithout c j l))) x)
    (Finset.mem_univ j)]
  have hz : highPeriodizedChart d k j
      (highFrameProfile (highFramePolynomial (highCoefficientWithout c j j))) x = 0 := by
    rw [highPeriodizedFrame_evaluation]
    simp [highCoefficientWithout]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
  have he : highCoefficientWithout c j l = c l := by
    funext γ
    exact ite_eq_right hlj
  rw [he]

theorem highCoefficientWithout_coefficient_ball {d k D : ℕ}
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ l, ∑ γ, |c l γ| ≤ R) :
    ∀ l, ∑ γ, |highCoefficientWithout c j l γ| ≤ R := by
  intro l
  by_cases hlj : l = j
  · simpa only [highCoefficientWithout, ite_eq_left hlj, abs_zero, Finset.sum_const_zero] using hR
  · simpa only [highCoefficientWithout, ite_eq_right hlj] using hc l

/-- Exact active-window amplitude of the actual WITHOUT-j field. -/
theorem highLocalFieldWithout_intrinsic_abs_bound {d D : ℕ}
    (C : ModelConstants d) (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (Cfr η : ℝ) (hCfr : highIntrinsicFrameConstant C ≤ Cfr) (hη : 0 ≤ η)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (hc : ∀ l, ∑ γ, |c l γ| ≤ Cfr⁻¹)
    (j : HighWindowLabels d k) (x : Covariate d) :
    |highLocalFieldWithout d k D η c j x| ≤ (2 : ℝ)^d*η := by
  have hCpos : 0 < Cfr := lt_of_lt_of_le (highIntrinsicFrameConstant_pos C) hCfr
  have hinv : Cfr⁻¹ ≤ (highIntrinsicFrameConstant C)⁻¹ :=
    (inv_le_inv₀ hCpos (highIntrinsicFrameConstant_pos C)).mpr hCfr
  have hmod := highCoefficientWithout_coefficient_ball c j (Cfr⁻¹) (inv_nonneg.mpr hCpos.le) hc
  have hP (l) : frameCoefficientL1 (highFramePolynomial (highCoefficientWithout c j l)) ≤
      (highIntrinsicFrameConstant C)⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans ((hmod l).trans hinv)
  rw [highLocalFieldWithout_eq_zero_block]
  have h := highFrameField_multiPartial_intrinsic_bound C k hk η _ hP
    (fun _ => (0 : Fin (C.order+1))) (by simp) x
  simp only [Fin.val_zero, Finset.sum_const_zero, multiPartial_zero_index, pow_zero,
    mul_one, abs_of_nonneg hη] at h
  exact h.trans_eq (mul_comm _ _)

/-- The paper's literal Reg amplitude guard gives its required offset range. -/
theorem highLocalFieldWithout_intrinsic_offset_guard {d D : ℕ}
    (C : ModelConstants d) (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (Cfr η ρ : ℝ) (hCfr : highIntrinsicFrameConstant C ≤ Cfr) (hη : 0 ≤ η)
    (hηρ : η ≤ ρ/(2 : ℝ)^(d+1))
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (hc : ∀ l, ∑ γ, |c l γ| ≤ Cfr⁻¹)
    (j : HighWindowLabels d k) (x : Covariate d) :
    |highLocalFieldWithout d k D η c j x| ≤ ρ/2 := by
  apply (highLocalFieldWithout_intrinsic_abs_bound C k hk Cfr η hCfr hη c hc j x).trans
  have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(d+1))).mp hηρ
  rw [pow_succ] at hmul
  linarith

end NearlyMinimax
