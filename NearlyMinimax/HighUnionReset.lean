module

public import NearlyMinimax.HighCenteredRowUnion
public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HistoryAppendMeasurable


@[expose] public section

/-! Full-mark raw state updates for the actual ordinary/fine-pair union.
The data contain only the row laws and reset functions; all probability,
measurability, interval and coefficient conclusions are proved below. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

structure HighUnionRowData (d k F : ℕ) (I : Type*) (E : I → Type*)
    [∀ i, MeasurableSpace (E i)] where
  rowLaw : (i : I) → Measure (E i)
  rowMass : I → ℝ
  rowActivation : (i : I) → E i → ℝ
  rowIntercept : (i : I) → E i → ℝ
  rowSlope : HighWindowLabels d k → (i : I) → E i → Covariate d → ℝ
  rowVector : (i : I) → E i → HighFrameIndex d F → ℝ
  rowTime : (i : I) → E i → ℝ

abbrev HighUnionMark {I : Type*} (E : I → Type*) := (Sigma E) ⊕ Unit

theorem highUnionMark_standardBorel {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] :
    StandardBorelSpace (HighUnionMark E) := by
  letI : StandardBorelSpace (Sigma E) := highRowReferenceUnion_standardBorel
  letI := upgradeStandardBorel (Sigma E)
  letI : BorelSpace ((Sigma E) ⊕ Unit) := packetSum_borelSpace
  infer_instance

section Reset
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] (R : HighUnionRowData d k F I E)

def highUnionLaw (δ : ℝ) : Measure (HighUnionMark E) :=
  highCenteredRowUnionLaw R.rowLaw R.rowMass δ

def highUnionActivation (δ : ℝ) : HighUnionMark E → ℝ :=
  highCenteredRowUnionActivation R.rowMass R.rowActivation δ

def highUnionIntercept (δ : ℝ) : HighUnionMark E → ℝ :=
  highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ

def highUnionSlope (j : HighWindowLabels d k) (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highCenteredRowUnionSlope (fun i e => R.rowSlope j i e x) e

def highUnionResponseVector : HighUnionMark E → HighFrameIndex d F → ℝ :=
  Sum.elim (fun e => R.rowVector e.1 e.2) (fun _ => 0)

def highUnionResponseTime : HighUnionMark E → ℝ :=
  Sum.elim (fun e => R.rowTime e.1 e.2) (fun _ => 0)

def highUnionResponseReset (e : HighUnionMark E) (c : HighFrameIndex d F → ℝ) :
    HighFrameIndex d F → ℝ :=
  coefficientReset c (highUnionResponseVector R e) (highUnionResponseTime R e)

def highUnionRawUpdate (δ : ℝ) (j : HighWindowLabels d k) (e : HighUnionMark E)
    (θ : HighRawState d k F) : HighRawState d k F :=
  rawPatchUpdate j (highTorusPatch d k j) (highUnionSlope R j e)
    (fun _ => highUnionIntercept R δ e) (highUnionResponseReset R e) θ

theorem highUnionLaw_probability [∀ i, IsProbabilityMeasure (R.rowLaw i)]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : IsProbabilityMeasure (highUnionLaw R δ) :=
  highCenteredRowUnionLaw_probability R.rowLaw R.rowMass hMass hTotal δ hδ0 hδ1

theorem highUnionActivation_measurable (hAct : ∀ i, Measurable (R.rowActivation i)) (δ : ℝ) :
    Measurable (highUnionActivation R δ) :=
  highCenteredRowUnionActivation_measurable R.rowMass R.rowActivation hAct δ

theorem highUnionActivation_centered (hMass : ∀ i, 0 ≤ R.rowMass i)
    (hAct : ∀ i, Measurable (R.rowActivation i))
    (hiAct : ∀ i, Integrable (R.rowActivation i) (R.rowLaw i))
    (hcAct : ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ e, highUnionActivation R δ e ∂highUnionLaw R δ) = 0 :=
  highCenteredRowUnionActivation_centered R.rowLaw R.rowMass hMass R.rowActivation
    hAct hiAct hcAct δ hδ hδ1

theorem highUnionIntercept_measurable (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ : ℝ) :
    Measurable (highUnionIntercept R δ) :=
  highCenteredRowUnionIntercept_measurable R.rowLaw R.rowMass R.rowIntercept hOffset δ

theorem highUnionSlope_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (j : HighWindowLabels d k) :
    Measurable (fun ex : HighUnionMark E × Covariate d => highUnionSlope R j ex.1 ex.2) := by
  let G : Sigma (fun i => E i × Covariate d) → ℝ := fun ex =>
    R.rowSlope j ex.1 ex.2.1 ex.2.2
  have hG : Measurable G := (historySigma_measurable_iff G).mpr (hSlope j)
  have hSigma : Measurable (fun ex : (Sigma E) × Covariate d =>
      R.rowSlope j ex.1.1 ex.1.2 ex.2) :=
    hG.comp (historySigmaProdMeasurableEquiv E (Covariate d)).measurable
  have h := (hSigma.sumElim (measurable_const (a := (0 : ℝ)))).comp
    (MeasurableEquiv.sumProdDistrib (Sigma E) Unit (Covariate d)).measurable
  convert h using 1
  funext ⟨e,x⟩
  cases e <;> rfl

theorem highUnionResponseVector_measurable
    (hVector : ∀ i γ, Measurable (fun e => R.rowVector i e γ)) (γ : HighFrameIndex d F) :
    Measurable (fun e => highUnionResponseVector R e γ) :=
  (rowSigmaFunction_measurable (fun i e => R.rowVector i e γ) (fun i => hVector i γ)).sumElim
    measurable_const

theorem highUnionResponseTime_measurable (hTime : ∀ i, Measurable (R.rowTime i)) :
    Measurable (highUnionResponseTime R) :=
  (rowSigmaFunction_measurable R.rowTime hTime).sumElim measurable_const

theorem highUnionRawUpdate_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (hOffset : ∀ i, Measurable (R.rowIntercept i))
    (hVector : ∀ i γ, Measurable (fun e => R.rowVector i e γ))
    (hTime : ∀ i, Measurable (R.rowTime i)) (δ : ℝ) (j : HighWindowLabels d k) :
    Measurable (fun eθ : HighUnionMark E × HighRawState d k F =>
      highUnionRawUpdate R δ j eθ.1 eθ.2) := by
  have hs (x : Covariate d) : Measurable (fun e => highUnionSlope R j e x) :=
    (highUnionSlope_joint_measurable R hSlope j).comp (measurable_id.prodMk measurable_const)
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro x
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, if_pos hx]
      exact ((hs x).comp measurable_fst).mul
        ((measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)) |>.add
        ((highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    · simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, if_neg hx]
      exact (measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)
  · apply measurable_pi_lambda
    intro l
    apply measurable_pi_lambda
    intro γ
    by_cases hl : l = j
    · subst l
      simp only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
        Function.update_self, highUnionResponseReset, coefficientReset]
      exact ((measurable_const.sub ((highUnionResponseTime_measurable R hTime).comp
          measurable_fst)).mul (by fun_prop)).add
        (((highUnionResponseTime_measurable R hTime).comp measurable_fst).mul
          ((highUnionResponseVector_measurable R hVector γ).comp measurable_fst))
    · simp only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate, Function.update_of_ne hl]
      fun_prop

theorem highUnionRawUpdate_commute [NeZero k] (δ : ℝ)
    (j l : HighWindowLabels d k) (hjl : l ∉ highNeighborLabels d k j)
    (e f : HighUnionMark E) (θ : HighRawState d k F) :
    highUnionRawUpdate R δ l f (highUnionRawUpdate R δ j e θ) =
      highUnionRawUpdate R δ j e (highUnionRawUpdate R δ l f θ) := by
  apply rawPatchUpdate_commute
  · intro h
    exact hjl (h ▸ highNeighborLabels_self_mem d k j)
  · exact highTorusPatch_disjoint_of_not_neighbor d k j l hjl

theorem highUnionResponseReset_ball (Cfr : ℝ) (hCfr : 0 < Cfr)
    (hVector : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹)
    (hTime : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1)
    (e : HighUnionMark E) (c : HighFrameIndex d F → ℝ)
    (hc : (∑ γ, |c γ|) ≤ Cfr⁻¹) :
    (∑ γ, |highUnionResponseReset R e c γ|) ≤ Cfr⁻¹ := by
  have hτ : highUnionResponseTime R e ∈ Icc (0 : ℝ) 1 := by
    cases e with
    | inl e => exact hTime e.1 e.2
    | inr e => simp [highUnionResponseTime]
  have hv : (∑ γ, |highUnionResponseVector R e γ|) ≤ Cfr⁻¹ := by
    cases e with
    | inl e => exact hVector e.1 e.2
    | inr e => simp [highUnionResponseVector, hCfr.le]
  exact coefficientReset_mem_ball Cfr c _ _ hτ hc hv

/-- The sole balancing branch is legal by the actual union intercept mean;
ordinary and fine-pair raw branches use their proved primitive reset bounds. -/
theorem highUnionReset_interval [∀ i, IsProbabilityMeasure (R.rowLaw i)]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (hOffset : ∀ i, Measurable (R.rowIntercept i))
    (a b : ℝ) (hOffsetBound : ∀ i e, R.rowIntercept i e ∈ Icc a b)
    (hRawLegal : ∀ j i e x v, v ∈ Icc a b →
      R.rowSlope j i e x * v + R.rowIntercept i e ∈ Icc a b)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (radius width : ℝ) (hRadius : 0 < radius) (ha1 : a + radius ≤ 1)
    (hb1 : 1 + radius ≤ b) (hWidth : b - a ≤ width) (hδWidth : δ * width ≤ radius / 2)
    (j : HighWindowLabels d k) (e : HighUnionMark E) (x : Covariate d)
    (v : ℝ) (hv : v ∈ Icc a b) :
    highUnionSlope R j e x * v + highUnionIntercept R δ e ∈ Icc a b := by
  cases e with
  | inl e => exact hRawLegal j e.1 e.2 x v hv
  | inr e =>
    simp only [highUnionSlope, highUnionIntercept, highCenteredRowUnionSlope,
      highCenteredRowUnionIntercept, balancedSlope, balancedIntercept, Sum.elim_inr,
      zero_mul, zero_add]
    letI := highRowReferenceUnion_probability R.rowLaw R.rowMass hMass hTotal
    exact balancedResetAnchor_mem a b radius width δ _ hRadius hδ0 hδ1
      ha1 hb1 hWidth hδWidth
      (boundedIntercept_mean_mem (highRowReferenceUnion R.rowLaw R.rowMass)
        (fun e : Sigma E => R.rowIntercept e.1 e.2)
        (rowSigmaFunction_measurable R.rowIntercept hOffset) a b (fun e => hOffsetBound e.1 e.2))

end Reset
end NearlyMinimax
