module

public import NearlyMinimax.HighRowReferenceUnion


@[expose] public section

/-! The paper's global tagged Xi reference construction: first mix the
absolute row laws with their true variation masses, then add exactly one
zero-weight corrective branch. The generator action and source activation
constant are preserved by actual positive-measure integral identities. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace (E j)]

def highCenteredRowUnionLaw (π : (j : J) → Measure (E j)) (B : J → ℝ) (δ : ℝ) :
    Measure ((Sigma E) ⊕ Unit) := balancedReferenceLaw (highRowReferenceUnion π B) δ

def highCenteredRowUnionActivation (B : J → ℝ) (w : (j : J) → E j → ℝ) (δ : ℝ) :
    (Sigma E) ⊕ Unit → ℝ := balancedActivation (highRowUnionActivation B w) δ

def highCenteredRowUnionIntercept (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (intercept : (j : J) → E j → ℝ) (δ : ℝ) : (Sigma E) ⊕ Unit → ℝ :=
  balancedIntercept (fun e : Sigma E => intercept e.1 e.2) δ
    (∫ e : Sigma E, intercept e.1 e.2 ∂highRowReferenceUnion π B)

def highCenteredRowUnionSlope (slope : (j : J) → E j → ℝ) : (Sigma E) ⊕ Unit → ℝ :=
  balancedSlope (fun e : Sigma E => slope e.1 e.2)

theorem highCenteredRowUnionLaw_probability (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure (highCenteredRowUnionLaw π B δ) := by
  letI := highRowReferenceUnion_probability π B hB hTotal
  exact balancedReferenceLaw_probability _ δ hδ0 hδ1

theorem highCenteredRowUnionActivation_centered (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) (hInt : ∀ j, Integrable (w j) (π j))
    (hCenter : ∀ j, (∫ e, w j e ∂π j) = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ e, highCenteredRowUnionActivation B w δ e ∂highCenteredRowUnionLaw π B δ) = 0 :=
  balancedActivation_integral_zero _ δ hδ hδ1 _ (highRowUnionActivation_measurable B w hw)
    (highRowUnionActivation_integrable π B w hw hInt)
    (highRowUnionActivation_centered π B hB w hw hInt hCenter)

theorem highCenteredRowUnionActivation_bound (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (w : (j : J) → E j → ℝ)
    (hw : ∀ j e, |w j e| ≤ B j) (δ : ℝ) (hδ : 0 < δ) (e : (Sigma E) ⊕ Unit) :
    |highCenteredRowUnionActivation B w δ e| ≤ highRowTotalMass B / δ := by
  apply balancedActivation_bound _ δ _ hδ hTotal.le
  intro e
  simpa only [div_one] using highRowUnionActivation_bound B hB hTotal 1 (by norm_num)
    w (by simpa only [div_one] using hw) e

/-- Actual source signed action on the global union, with one corrective
zero-weight branch and genuine row signed measures. -/
theorem highCenteredRowUnion_signed_action (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 < B j) (hTotal : 0 < highRowTotalMass B)
    (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (hInt : ∀ j, Integrable (w j) (π j)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (F : (Sigma E) ⊕ Unit → ℝ) (hF : Measurable F) (M : ℝ) (hBound : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, highCenteredRowUnionActivation B w δ e * F e ∂highCenteredRowUnionLaw π B δ) =
      ∑ j, ∫ᵛ e, F (Sum.inl ⟨j,e⟩) ∂<•(π j).withDensityᵥ (w j) := by
  have hUnionInt := highRowUnionActivation_integrable π B w hw hInt
  have hUnionFInt := hUnionInt.mul_bdd (hF.comp measurable_inl).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hBound (Sum.inl e)))
  rw [highCenteredRowUnionActivation, highCenteredRowUnionLaw,
    balancedActivation_integral _ δ hδ hδ1 _ (highRowUnionActivation_measurable B w hw) F hF hUnionFInt]
  have h := highRowUnion_signed_action π B hB hTotal w hw hInt
    (fun e => F (Sum.inl e)) (hF.comp measurable_inl) M (fun e => hBound (Sum.inl e))
  rw [highRowUnionSignedMeasure, signedDensity_integral _ _ hUnionInt
    (highRowUnionActivation_measurable B w hw) (fun e : Sigma E => F (Sum.inl e))
    (hF.comp measurable_inl) M
    (fun e => hBound (Sum.inl e))] at h
  exact h

theorem highCenteredRowUnionActivation_measurable (B : J → ℝ)
    (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j)) (δ : ℝ) :
    Measurable (highCenteredRowUnionActivation B w δ) :=
  balancedActivation_measurable _ (highRowUnionActivation_measurable B w hw) δ

theorem highCenteredRowUnionSlope_measurable (slope : (j : J) → E j → ℝ)
    (hSlope : ∀ j, Measurable (slope j)) : Measurable (highCenteredRowUnionSlope slope) :=
  balancedSlope_measurable _ (rowSigmaFunction_measurable slope hSlope)

theorem highCenteredRowUnionIntercept_measurable (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j)) (δ : ℝ) :
    Measurable (highCenteredRowUnionIntercept π B intercept δ) :=
  balancedIntercept_measurable _ (rowSigmaFunction_measurable intercept hIntercept) δ _

theorem highCenteredRowUnionSlope_integral_zero (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope : (j : J) → E j → ℝ) (hSlope : ∀ j, Measurable (slope j))
    (hiSlope : ∀ j, Integrable (slope j) (π j))
    (hCenter : ∀ j, (∫ e, slope j e ∂π j) = 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ e, highCenteredRowUnionSlope slope e ∂highCenteredRowUnionLaw π B δ) = 0 :=
  balancedSlope_integral_zero _ δ hδ0 hδ1 _ (rowSigmaFunction_measurable slope hSlope)
    (highRowReferenceUnion_integrable π B _ (rowSigmaFunction_measurable slope hSlope) hiSlope)
    (highRowReferenceUnion_integral_common_mean π B hB hTotal slope hSlope hiSlope 0 hCenter)

theorem highCenteredRowUnionIntercept_integral_one (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B)
    (intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j))
    (a b : ℝ) (hBound : ∀ j e, intercept j e ∈ Icc a b)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∫ e, highCenteredRowUnionIntercept π B intercept δ e ∂highCenteredRowUnionLaw π B δ) = 1 := by
  letI := highRowReferenceUnion_probability π B hB hTotal
  exact balancedIntercept_integral_one _ δ hδ0 hδ1 _
    (rowSigmaFunction_measurable intercept hIntercept)
    (boundedIntercept_integrable (highRowReferenceUnion π B) _
      (rowSigmaFunction_measurable intercept hIntercept) a b (fun e => hBound e.1 e.2))

theorem highCenteredRowUnion_expected_reset_one (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B)
    (slope intercept : (j : J) → E j → ℝ)
    (hSlope : ∀ j, Measurable (slope j)) (hIntercept : ∀ j, Measurable (intercept j))
    (hiSlope : ∀ j, Integrable (slope j) (π j))
    (hCenter : ∀ j, (∫ e, slope j e ∂π j) = 0)
    (a b : ℝ) (hBound : ∀ j e, intercept j e ∈ Icc a b)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (p : ℝ) :
    (∫ e, highCenteredRowUnionSlope slope e * p + highCenteredRowUnionIntercept π B intercept δ e
      ∂highCenteredRowUnionLaw π B δ) = 1 := by
  letI := highRowReferenceUnion_probability π B hB hTotal
  have hAi := highRowReferenceUnion_integrable π B _
    (rowSigmaFunction_measurable slope hSlope) hiSlope
  have hBi := boundedIntercept_integrable (highRowReferenceUnion π B)
    (fun e : Sigma E => intercept e.1 e.2) (rowSigmaFunction_measurable intercept hIntercept)
    a b (fun e => hBound e.1 e.2)
  have hAc := highRowReferenceUnion_integral_common_mean π B hB hTotal slope hSlope hiSlope 0 hCenter
  exact balancedReferenceLaw_expected_reset_one _ δ hδ0 hδ1 _ _
    (rowSigmaFunction_measurable slope hSlope) (rowSigmaFunction_measurable intercept hIntercept)
    hAi hBi hAc p

/-- The source's single corrective intercept is legal at its uniform
resolution threshold, for the actual total union intercept mean. -/
theorem highCenteredRowUnionIntercept_source_interval {d : ℕ} (C : ModelConstants d)
    (π : (j : J) → Measure (E j)) [∀ j, IsProbabilityMeasure (π j)]
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j))
    (M : ℝ) (hM : highCenterResolutionThreshold C ≤ M)
    (hBound : ∀ j e, intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    ∀ e, highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := highRowReferenceUnion_probability π B hB hTotal
  have hg := highCenterResolution_guards C M hM
  have hq := boundedIntercept_mean_mem (highRowReferenceUnion π B)
    (fun e : Sigma E => intercept e.1 e.2) (rowSigmaFunction_measurable intercept hIntercept)
    (C.densityLower+1/M) (C.densityUpper-1/M) (fun e => hBound e.1 e.2)
  intro e
  cases e with
  | inl e => exact hBound e.1 e.2
  | inr u =>
    exact sourceBalancedResetAnchor_mem C M _ (by linarith) hg.2 hq

/-- Source global density reset legality, including the one corrective branch. -/
theorem highCenteredRowUnion_reset_source_legal {d : ℕ} (C : ModelConstants d)
    (π : (j : J) → Measure (E j)) [∀ j, IsProbabilityMeasure (π j)]
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j))
    (M : ℝ) (hM : highCenterResolutionThreshold C ≤ M)
    (hBound : ∀ j e, intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (hlegal : ∀ j e p, p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
      slope j e*p+intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (e : (Sigma E) ⊕ Unit) (p : ℝ)
    (hp : p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highCenteredRowUnionSlope slope e*p+highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  cases e with
  | inl e => exact hlegal e.1 e.2 p hp
  | inr u =>
    simpa only [highCenteredRowUnionSlope, balancedSlope, Sum.elim_inr, zero_mul, zero_add]
      using highCenteredRowUnionIntercept_source_interval C π B hB hTotal intercept hIntercept
        M hM hBound (Sum.inr u)

theorem highCenteredRowUnionActivation_attains_bound (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (w : (j : J) → E j → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (j : J) (e : E j) (he : |w j e| = B j) :
    |highCenteredRowUnionActivation B w δ (Sum.inl ⟨j,e⟩)| = highRowTotalMass B / δ := by
  have h := highRowUnionActivation_attains_bound B hB hTotal 1 (by norm_num) w j e
    (by simpa only [div_one] using he)
  change |highRowUnionActivation B w ⟨j,e⟩ / δ| = _
  rw [abs_div, abs_of_pos hδ]
  simpa only [div_one] using congrArg (fun x : ℝ => x / δ) h

end

/-- Positive actual variation yields a genuine mark attaining the absolute
activation mass, so the eventual source activation supremum is exact. -/
theorem absoluteActivation_attains_mass {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w : E → ℝ) (hpos : 0 < signedMarkMass μ w) :
    ∃ e, |absoluteActivation μ w e| = signedMarkMass μ w := by
  have hex : ∃ e, w e ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : signedMarkMass μ w = 0 := by simp only [signedMarkMass, h, abs_zero, integral_zero]
    linarith
  obtain ⟨e, he⟩ := hex
  refine ⟨e, ?_⟩
  rw [absoluteActivation, abs_mul, abs_of_pos hpos, abs_div, abs_abs,
    div_self (abs_ne_zero.mpr he), mul_one]

end NearlyMinimax
