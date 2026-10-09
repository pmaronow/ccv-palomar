module

public import NearlyMinimax.HighIntrinsicFieldLegality


@[expose] public section

/-! Full original-model legality for literal intrinsic-ball raw frame states.
This specializes the true global norm, numeric mass normalization and ternary
response moment identities; model membership is not a premise. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

theorem highFrame_intrinsic_normalized_parameter_admissible {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧
      ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ cf : ℝ, 0 ≤ cf →
      highWindowHolderConstant C * cf ≤ C.holderBound →
      ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ (highIntrinsicFrameConstant C)⁻¹) →
      cf * (k : ℝ) ^ (-C.smoothness) ≤ η0 →
      ∀ M cm : ℝ, 2 ≤ M → 0 ≤ cm → cm ≤ 1 / C.densityUpper →
      ∀ p : Covariate d → ℝ, Measurable p →
      (∀ᵐ x ∂cubeVolume d,
        C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M) →
      |highRawDensityMass p - 1| ≤ cm / M →
      ∀ V : ℝ, |V - Q.v| ≤ Q.ρ →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      ∃ hq : ∀ x y, 0 ≤ ternaryMass Q.a (F x) V y,
        Admissible C (normalizedDensityTernaryParameter p F Q.a V
          (highFrameField_contDiff d k _ P).continuous.measurable Q.a_pos.ne' hq) := by
  obtain ⟨η0, hη0, hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨η0, hη0, ?_⟩
  intro k hk0 hk cf hcf hbudget P hP hη M cm hM hcm hcmU p hp hraw hmass V hV
  letI := hk0
  let η := cf * (k : ℝ) ^ (-C.smoothness)
  let F := highFrameField d k η P
  have hη0' : 0 ≤ η := by dsimp [η]; positivity
  obtain ⟨_, hsupη⟩ := hguard η hη0' hη
  obtain ⟨hvalue, _, _, hnorm⟩ := highFrameField_intrinsic_original_model_bounds C k hk cf hcf P hP
  have hf (x : Covariate d) : |F x| ≤ Q.ρ := by
    exact (hvalue x).trans (hsupη.trans (by linarith [Q.ρ_pos]))
  have hlegal (x : Covariate d) := Q.legal (F x) V (hf x) hV
  have hq : ∀ x y, 0 ≤ ternaryMass Q.a (F x) V y :=
    fun x y => Q.c_pos.le.trans ((hlegal x).2.2.1 y)
  refine ⟨hq, ?_⟩
  have hF := highFrameField_contDiff d k η P
  have hM0 : 0 < M := by linarith
  have hint := highRawDensity_integrable C M hM0 p hp hraw
  have hp0 : 0 ≤ᵐ[cubeVolume d] p := by
    filter_upwards [hraw] with x hx
    change 0 ≤ p x
    linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hmass0 : 0 < highRawDensityMass p := lt_of_lt_of_le (by norm_num)
    (high_raw_mass_lower C M cm (highRawDensityMass p) hM hcm hcmU hmass)
  refine ⟨highNormalizedDensity_measurable p hp, hF.continuous.measurable,
    highNormalizedDensity_bounds C M cm hM hcm hcmU p hraw hmass,
    highNormalizedDensity_normalized p hint hp0 hmass0, ?_,
    (hlegal 0).1.le, (hlegal 0).2.1.le, ?_⟩
  · refine ⟨F, fun _ _ => rfl, (hF.of_le (by simp)).contDiffOn, ?_⟩
    exact (hnorm C.domain).trans (ENNReal.ofReal_le_ofReal hbudget)
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ternary_error_integrable Q.a V F hF.continuous.measurable x _,
      ternary_error_integrable Q.a V F hF.continuous.measurable x _,
      ternary_error_integrable Q.a V F hF.continuous.measurable x _,
      ternary_error_mean Q.a V F hF.continuous.measurable x Q.a_pos.ne' (hq x),
      ternary_error_variance Q.a V F hF.continuous.measurable x Q.a_pos.ne' (hq x), ?_⟩
    exact (ternary_error_fourth Q.a V F hF.continuous.measurable x Q.a_pos.ne' (hq x)).trans_le
      (by simpa only [ternary_fourth_central_moment _ _ _ Q.a_pos.ne'] using (hlegal x).2.2.2)


end NearlyMinimax
