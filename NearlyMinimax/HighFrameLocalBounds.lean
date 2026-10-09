module

public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! Actual coordinatewise chart bounds for the finite polynomial frame. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem highFrameFeature_abs_le_one {d F : ℕ} (x : Covariate d)
    (hx : ∀ i, |x i| ≤ 2) (γ : HighFrameIndex d F) :
    |highFrameFeature x γ| ≤ 1 := by
  unfold highFrameFeature
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_pow]
    have hb : |x i / 8| ≤ 1 := by
      rw [abs_div]
      rw [show |(8 : ℝ)| = 8 by norm_num]
      apply (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr
      exact (hx i).trans (by norm_num)
    exact pow_le_one₀ (abs_nonneg _) hb

theorem highFrameProfile_abs_le_coefficients {d F : ℕ} (x : Covariate d)
    (hx : ∀ i, |x i| ≤ 2) (v : HighFrameIndex d F → ℝ) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ ∑ γ, |v γ| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (highFrameFeature_abs_le_one x hx γ) (abs_nonneg _)).trans_eq (one_mul _)

theorem highFrameProfile_abs_le_one {d F : ℕ} (C : ℝ) (hC : 1 ≤ C)
    (x : Covariate d) (hx : ∀ i, |x i| ≤ 2) (v : HighFrameIndex d F → ℝ)
    (hv : ∑ γ, |v γ| ≤ C⁻¹) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ 1 :=
  (highFrameProfile_abs_le_coefficients x hx v).trans (hv.trans (inv_le_one_of_one_le₀ hC))

theorem highFrameCoefficientRegression_abs_le {d n F : ℕ}
    (C η ρ : ℝ) (hC : 1 ≤ C) (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (g w : Fin n → ℝ) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) (i : Fin n) :
    |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ := by
  have hprof := highFrameProfile_abs_le_one C hC (U i) (hU i) c hc
  have hwη : |η*w i| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one _)
  have hterm : |η*w i*(∑ γ, highFrameFeature (U i) γ * c γ)| ≤ η := by
    rw [abs_mul]
    exact (mul_le_mul hwη hprof (abs_nonneg _) hη).trans_eq (mul_one _)
  unfold coefficientRegression
  exact (abs_add_le _ _).trans (by linarith only [hg i, hterm, hηρ])

end NearlyMinimax
