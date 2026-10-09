module

public import NearlyMinimax.HighCompleteSourceTail


@[expose] public section

/-! Conversion of the true positive activated complete-source reference
law into the genuine signed atom packets. All spatial/field carriers and
finite response marks remain in their actual signed measures. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

def sourceRowSignedMeasure (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SignedMeasure (SourceRowMark d D M q a b C lam ℓ N μ i)
  | .inl .unit => highPacketSignedMeasure (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .inl .coarse => highPacketSignedMeasure (finePairTimeFieldMeasure d 0 ℓ) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inl .fine => finePairPacketSignedMeasure (finePairTimeFieldMeasure d ℓ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inr (.inl _) => highPacketSignedMeasure (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D)
  | .inr (.inr i) => higherBandSignedRow d (higherBandFamilyTarget i.val)
      (higherBandFamilyGuardDegree M i.val) D q a b C lam ℓ
      (higherBandFamilyUpper d ℓ N μ i.val) i.val.2

theorem sourceRow_activated_signed_action (d : ℕ) [NeZero d] (k D M q : ℕ)
    (a b C lam ℓ N μ : ℝ)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (F : SourceRowMark d D M q a b C lam ℓ N μ i → ℝ) (hF : Measurable F)
    (L : ℝ) (hFbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, (sourceRowData d k D M q a b C lam ℓ N μ).rowActivation i e * F e
      ∂(sourceRowData d k D M q a b C lam ℓ N μ).rowLaw i) =
      ∫ᵛ e, F e ∂<•sourceRowSignedMeasure d k D M q a b C lam ℓ N μ i := by
  cases i with
  | inl p =>
    cases p
    · exact absoluteMarkLaw_signed_action ((Measure.dirac ()).prod Measure.count)
        (highPacketMarkWeight a b D 2 D q C (fun _ => finePairUnitMatrix d D))
        (highPacketMarkWeight_integrable (Measure.dirac ()) a b D 2 D q C _
          (fun _ _ => measurable_const) (integrable_const _))
        (highPacketMarkWeight_measurable a b D 2 D q C _ (fun _ _ => measurable_const))
        (hpos (.inl .unit)) F hF L hFbound
    · exact absoluteMarkLaw_signed_action ((finePairTimeFieldMeasure d 0 ℓ).prod Measure.count)
        (highPacketMarkWeight a b D 2 D q C (finePairTimeMatrix d (finePairDistanceMatrix d D)))
        (highPacketMarkWeight_integrable _ a b D 2 D q C _ (finePairTimeMatrix_measurable d _)
          (finePairTimeMatrix_cost_integrable d 0 ℓ _))
        (highPacketMarkWeight_measurable a b D 2 D q C _ (finePairTimeMatrix_measurable d _))
        (hpos (.inl .coarse)) F hF L hFbound
    · exact absoluteMarkLaw_signed_action ((finePairTimeFieldMeasure d ℓ N).prod Measure.count)
        (finePairPacketWeight a b M q C (finePairTimeMatrix d (finePairDistanceMatrix d D)))
        (finePairPacketWeight_integrable _ a b M q C _ (finePairTimeMatrix_measurable d _)
          (finePairTimeMatrix_cost_integrable d ℓ N _))
        (finePairPacketWeight_measurable a b M q C _ (finePairTimeMatrix_measurable d _))
        (hpos (.inl .fine)) F hF L hFbound
  | inr i =>
    cases i with
    | inl _ =>
      exact absoluteMarkLaw_signed_action ((Measure.dirac ()).prod Measure.count)
        (highPacketMarkWeight a b D 1 D q C (fun _ => finePairUnitMatrix d D))
        (highPacketMarkWeight_integrable (Measure.dirac ()) a b D 1 D q C _
          (fun _ _ => measurable_const) (integrable_const _))
        (highPacketMarkWeight_measurable a b D 1 D q C _ (fun _ _ => measurable_const))
        (hpos (.inr (.inl ()))) F hF L hFbound
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := higherBandFamilyGuardDegree M i.val
      let T := higherBandFamilyUpper d ℓ N μ i.val
      letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
      exact absoluteMarkLaw_signed_action ((higherBandCarrierMeasure d r ℓ T i.val.2).prod Measure.count)
        (highPacketMarkWeight a b m r D q C (higherBandCarrierAmplitude d r D lam i.val.2))
        (highPacketMarkWeight_integrable _ a b m r D q C _
          (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
          (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2))
        (highPacketMarkWeight_measurable a b m r D q C _
          (higherBandCarrierAmplitude_measurable d r D lam i.val.2))
        (hpos (.inr (.inr i))) F hF L hFbound

/-- The entire canonical source generator is an actual finite sum of
its constructed signed packet integrals, with numerical source guards. -/
theorem completeSourceUnion_signed_action {d k D M q : ℕ} [NeZero d]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (F : HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
      (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ) → ℝ) (hF : Measurable F)
    (L : ℝ) (hFbound : ∀ e, ‖F e‖ ≤ L) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e*F e ∂highUnionLaw R (highCenterMix C)) =
      ∑ i, ∫ᵛ e, F (Sum.inl ⟨i,e⟩)
        ∂<•sourceRowSignedMeasure d k D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ i := by
  dsimp only
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr
    (by linarith) lam ℓ N μ hℓ hℓN
  rw [highUnionSource_bounded_action C R G hpos F hF L hFbound]
  apply Finset.sum_congr rfl
  intro i _
  exact sourceRow_activated_signed_action d k D M q a b Cfr lam ℓ N μ hpos i
    (fun e => F (Sum.inl ⟨i,e⟩))
    (hF.comp (measurable_inl.comp (rowSigmaMk_measurable i))) L (fun e => hFbound _)

end NearlyMinimax
