module

public import NearlyMinimax.HighSourceCanonicalAction
public import NearlyMinimax.AffineNuisanceNumerator


@[expose] public section

/-! The actual complete tagged union action at arbitrary legal chart
nuisance values, independent of any canonical history representation. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

theorem completeSourceAffineAction_eq_signed_first_action
    {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k) (x : Fin n → Covariate d)
    (p : Fin n → ℝ)
    (hp : ∀ u, p u ∈ Icc (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)))
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ Cfr⁻¹)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) (hmΦ : Measurable Φ)
    (B : ℝ) (hB : 0 ≤ B) (hΦ : ∀ v : HighFrameIndex d D → ℝ,
      (∑ γ, |v γ|) ≤ Cfr⁻¹ → |Φ v| ≤ B) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e *
      ((∏ u, (highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e)) *
        Φ (highUnionResponseReset R e c)) ∂highUnionLaw R (highCenterMix C)) =
      completeSourceSignedFirstAction (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) lam ℓ N μ D M q Cfr
        (fun u => highLocalCoordinates d k j (x u)) p c Φ := by
  dsimp only
  let ad := C.densityLower+1/(M : ℝ)
  let bd := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  let U := fun u : Fin n => highLocalCoordinates d k j (x u)
  let O := fun e => (∏ u, (highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e))*
    Φ (highUnionResponseReset R e c)
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) :=
    highUnionMark_standardBorel
  have hmCoef : Measurable (fun e => highUnionResponseReset R e c) := by
    apply measurable_pi_iff.mpr
    intro γ
    unfold highUnionResponseReset coefficientReset
    exact (measurable_const.sub (highUnionResponseTime_measurable R G.time_measurable)).mul
      measurable_const |>.add ((highUnionResponseTime_measurable R G.time_measurable).mul
        (highUnionResponseVector_measurable R G.vector_measurable γ))
  have hmO : Measurable O := (Finset.measurable_fun_prod _ (fun u _ =>
    (((highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_id.prodMk measurable_const)).mul_const (p u)).add
        (highUnionIntercept_measurable R G.intercept_measurable (highCenterMix C)))).mul (hmΦ.comp hmCoef)
  have hMp : 0 < (M : ℝ) := by
    linarith [(highCenterResolution_guards C (M : ℝ) G.resolution).1]
  have hresetBound (e) (u) :
      |highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e| ≤ C.densityUpper := by
    have hh := highUnionSource_reset_interval C R G j e (x u) (p u) (hp u)
    rw [abs_of_nonneg (by linarith [hh.1,C.densityLower_pos,one_div_pos.mpr hMp])]
    linarith [hh.2,one_div_pos.mpr hMp]
  have hOb (e) : ‖O e‖ ≤ C.densityUpper^n*B := by
    change |(∏ u, (highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e))*Φ _| ≤ _
    rw [abs_mul]
    exact mul_le_mul (finite_density_product_abs_bound _ C.densityUpper
      (lt_trans zero_lt_one C.one_lt_densityUpper).le (hresetBound e))
      (hΦ _ (highUnionResponseReset_ball R Cfr (by linarith) G.vector_ball G.time_interval e c hc))
      (abs_nonneg _) (pow_nonneg (lt_trans zero_lt_one C.one_lt_densityUpper).le n)
  have hO (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) :
      O (Sum.inl ⟨i,e⟩) = (∏ u, (R.rowSlope j i e (x u)*p u+R.rowIntercept i e))*
        Φ (coefficientReset c (R.rowVector i e) (R.rowTime i e)) := by
    rfl
  rw [completeSourceUnion_signed_action C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN O hmO
    (C.densityUpper^n*B) hOb]
  change (∑ i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ,
      ∫ᵛ e, O (Sum.inl ⟨i,e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ i) =
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q Cfr U p c Φ
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  have hunit : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.unit,e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .unit)) =
      finePairUnitFirstAction ad bd D q Cfr p c Φ := by
    unfold finePairUnitFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,highPacketSlope,highPacketIntercept,
      highPacketObservable,localDensityReset]
    ring
  have hcoarse : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.coarse,e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .coarse)) =
      finePairCoarseFirstAction ad bd ℓ D q Cfr U p c Φ := by
    unfold finePairCoarseFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,highPacketSlope,highPacketIntercept,
      highPacketObservable,localDensityReset,U]
    ring
  have hfine : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.fine,e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .fine)) =
      finePairFineFirstAction ad bd ℓ N M q Cfr U p c Φ := by
    unfold finePairFineFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,finePairPacketSlope,finePairPacketIntercept,
      finePairPacketObservable,finePairDensityReset,U]
    ring
  have hsingle : (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inl ()),e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inr (.inl ()))) =
      singletonFirstAction ad bd D q Cfr p c Φ := by
    unfold singletonFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,singletonRowData,
      highPacketSlope,highPacketIntercept,highPacketObservable,localDensityReset]
    ring
  have hhigher (i : HigherBandFamilyIndex d D M q ad bd Cfr lam ℓ N μ) :
      (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inr i),e⟩)
        ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inr (.inr i))) =
      higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q Cfr i.val.2 U p c Φ := by
    unfold higherBandFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,higherBandFamilyComponent,
      higherBandRowData,highPacketSlope,highPacketIntercept,highPacketObservable,localDensityReset,U]
    ring
  have htags : (Finset.univ : Finset FinePairRowTag) = {.unit,.coarse,.fine} := by decide
  simp only [htags]
  simp [hunit,hcoarse,hfine,hsingle,hhigher,Fintype.sum_unique,
    completeSourceSignedFirstAction,finePairThreeRowFirstAction,add_assoc]

end NearlyMinimax
