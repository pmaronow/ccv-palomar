module

public import NearlyMinimax.HighPeriodizedFrame
public import NearlyMinimax.MultiIndexCount


@[expose] public section

/-! Original-model legality of the actual high-regime polynomial frame fields. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

def highWindowHolderConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 : ℝ) ^ d * (((d + C.order).choose d : ℝ) + 2)

theorem highWindowHolderConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < highWindowHolderConstant C := by
  unfold highWindowHolderConstant
  positivity

/-- With the original binomial count, the full norm constant is exactly
the manuscript's C_w. -/
theorem highFrameField_original_model_bounds {d : ℕ} (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ) ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * ((2 : ℝ) ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (highWindowHolderConstant C * cf)) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_model_bounds C
  refine ⟨Cfr, hCfr, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  obtain ⟨hv, hs, hm, _⟩ := hbound k hk0 hk cf hcf P hP
  refine ⟨hv, hs, hm, ?_⟩
  intro U
  have hh := holderNorm_of_global_mixed_bounds_binomial U _ C.order C.alpha
    ((2 : ℝ) ^ d * cf) (2 * ((2 : ℝ) ^ d * cf)) (by positivity) (by positivity) hs hm
  convert hh using 1
  congr 1
  unfold highWindowHolderConstant
  ring

theorem highFrame_ternary_amplitude_guards {d : ℕ} {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 ≤ η → η ≤ η0 →
      η ^ 2 ≤ Q.ρ ∧ (2 : ℝ) ^ d * η ≤ Q.ρ / 2 := by
  let η0 := min (Real.sqrt Q.ρ) (Q.ρ / (2 * (2 : ℝ) ^ d))
  have hη0 : 0 < η0 := by
    dsimp [η0]
    exact lt_min (Real.sqrt_pos.2 Q.ρ_pos) (div_pos Q.ρ_pos (by positivity))
  refine ⟨η0, hη0, ?_⟩
  intro η hη hηU
  have hηsqrt : η ≤ Real.sqrt Q.ρ := hηU.trans (min_le_left _ _)
  have hηρ : η ≤ Q.ρ / (2 * (2 : ℝ) ^ d) := hηU.trans (min_le_right _ _)
  constructor
  · nlinarith [Real.sq_sqrt Q.ρ_pos.le, Real.sqrt_nonneg Q.ρ]
  · have h := (le_div_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ d)).mp hηρ
    nlinarith

/-- Every raw frame state satisfying the stated numeric and mass guards
gives a genuine member of the original model.  No derivative, norm,
moment or model-membership claim is assumed. -/
theorem highFrame_normalized_parameter_admissible {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ cf : ℝ, 0 ≤ cf →
      highWindowHolderConstant C * cf ≤ C.holderBound →
      ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
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
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0, hη0, hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr, η0, hCfr, hη0, ?_⟩
  intro k hk0 hk cf hcf hbudget P hP hη M cm hM hcm hcmU p hp hraw hmass V hV
  letI := hk0
  let η := cf * (k : ℝ) ^ (-C.smoothness)
  let F := highFrameField d k η P
  have hη0' : 0 ≤ η := by dsimp [η]; positivity
  obtain ⟨_, hsupη⟩ := hguard η hη0' hη
  obtain ⟨hvalue, _, _, hnorm⟩ := hbound k hk0 hk cf hcf P hP
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
