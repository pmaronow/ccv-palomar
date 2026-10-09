module

public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.HighWindowGeometry


@[expose] public section

/-! Actual finite feature expansions and joint measurability of frame fields. -/
noncomputable section
open Set Function MeasureTheory MvPolynomial
open scoped BigOperators ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def highFrameMonomial {d D : ℕ} (γ : HighFrameIndex d D) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.monomial (polynomialBoxExponent γ.val) 1

theorem highFrameProfile_evaluation {d D : ℕ} (c : HighFrameIndex d D → ℝ) (x : Covariate d) :
    highFrameProfile (highFramePolynomial c) x =
      ∑ γ, c γ * highFrameProfile (highFrameMonomial γ) x := by
  unfold highFrameProfile
  rw [highFramePolynomial_scaled_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hm : MvPolynomial.eval x (frameScaledPolynomial (highFrameMonomial γ)) =
      highFrameFeature x γ := by
    rw [frameScaledPolynomial_eval]
    unfold highFrameMonomial highFrameFeature
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [polynomial_box_exponent_apply]
  rw [hm]
  ring

theorem highPeriodizedFrame_evaluation (d k D : ℕ) (j : HighWindowLabels d k)
    (c : HighFrameIndex d D → ℝ) (x : Covariate d) :
    highPeriodizedChart d k j (highFrameProfile (highFramePolynomial c)) x =
      ∑ γ, c γ * highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x := by
  have hfinite (γ : HighFrameIndex d D) : HasFiniteSupport (fun z : Fin d → ℤ =>
      c γ * (if (∀ r, (z r : ZMod k) = j r) then
        highFrameProfile (highFrameMonomial γ) (fun r => (k : ℝ) * x r - z r) else 0)) := by
    apply HasFiniteSupport.mul_right (fun _ => c γ)
    exact (highPeriodizedChart_locallyFinite d k j _
      (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))).point_finite x
  unfold highPeriodizedChart
  calc
    _ = ∑ᶠ z : Fin d → ℤ, ∑ γ : HighFrameIndex d D,
        c γ * (if (∀ r, (z r : ZMod k) = j r) then
          highFrameProfile (highFrameMonomial γ) (fun r => (k : ℝ) * x r - z r) else 0) := by
      apply finsum_congr
      intro z
      by_cases hz : ∀ r, (z r : ZMod k) = j r
      · simp only [ite_eq_left hz]
        exact highFrameProfile_evaluation c _
      · simp only [ite_eq_right hz, mul_zero, Finset.sum_const_zero]
    _ = ∑ γ : HighFrameIndex d D, ∑ᶠ z : Fin d → ℤ,
        c γ * (if (∀ r, (z r : ZMod k) = j r) then
          highFrameProfile (highFrameMonomial γ) (fun r => (k : ℝ) * x r - z r) else 0) :=
      (sum_finsum_comm Finset.univ _ (fun γ _ => hfinite γ)).symm
    _ = _ := by simp_rw [← mul_finsum]

theorem highFrameField_finite_evaluation (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Covariate d) :
    highFrameField d k η (fun j => highFramePolynomial (c j)) x =
      η * ∑ j, ∑ γ, c j γ * highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x := by
  unfold highFrameField
  simp_rw [highPeriodizedFrame_evaluation]

theorem highFrameField_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : Ω → HighWindowLabels d k → HighFrameIndex d D → ℝ) (hc : Measurable c) :
    Measurable (fun ωx : Ω × Covariate d =>
      highFrameField d k η (fun j => highFramePolynomial (c ωx.1 j)) ωx.2) := by
  simp_rw [highFrameField_finite_evaluation]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j hj
  apply Finset.measurable_sum
  intro γ hγ
  have hcoef : Measurable (fun ωx : Ω × Covariate d => c ωx.1 j γ) :=
    ((measurable_pi_apply γ).comp ((measurable_pi_apply j).comp hc)).comp measurable_fst
  have hchart : Measurable (fun ωx : Ω × Covariate d =>
      highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) ωx.2) :=
    (highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (highFrameMonomial γ))
      (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))).continuous.measurable.comp
        measurable_snd
  exact hcoef.mul hchart

end NearlyMinimax
