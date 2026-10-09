module

public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.FinePairRowAnnihilation
public import NearlyMinimax.HighUnionSourceGeometry


@[expose] public section

/-! Genuine complete fine-pair union mass-indicator annihilation. The
response coordinates are summed out of the actual signed packets; no
invariant-law or conditional score equality is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

abbrev FinePairRowDensityMark (d D M : ℕ) : FinePairRowTag → Type
  | .unit => Unit × HighDensityMarkIndex D 2 D
  | .coarse => (ℝ × FinePairFieldMark d) × HighDensityMarkIndex D 2 D
  | .fine => (ℝ × FinePairFieldMark d) × FinePairDensityIndex M

instance (d D M : ℕ) (i : FinePairRowTag) : MeasurableSpace (FinePairRowDensityMark d D M i) := by
  cases i <;> dsimp only [FinePairRowDensityMark] <;> infer_instance

def finePairRowDensityProj (d D M q : ℕ) (i : FinePairRowTag) :
    FinePairRowMark d D M q i → FinePairRowDensityMark d D M i := by
  cases i <;> exact fun e => (e.1,e.2.1)

def finePairRowWithResponse (d D M q : ℕ) (i : FinePairRowTag)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    FinePairRowDensityMark d D M i → FinePairRowMark d D M q i := by
  cases i <;> exact fun e => (e.1,(e.2,r))

theorem finePairRowWithResponse_measurable (d D M q : ℕ) (i : FinePairRowTag)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    Measurable (finePairRowWithResponse d D M q i r) := by
  cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

theorem finePairRow_density_observable_zero (d : ℕ) [NeZero d] (D M q : ℕ)
    (a b C T₀ N : ℝ) (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
    (i : FinePairRowTag) (F : FinePairRowDensityMark d D M i → ℝ) (hF : Measurable F)
    (L : ℝ) (hL : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, finePairRowActivation d D M q a b C T₀ N i e *
      F (finePairRowDensityProj d D M q i e) ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  cases i
  · exact highPacketAbsoluteLaw_density_observable_zero (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
      (hpos .unit) F hF L hL
  · exact highPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d 0 T₀)
      a b D 2 D q C _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse) F hF L hL
  · exact finePairPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d T₀ N)
      a b M q C _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine) F hF L hL


/-- True complete-union action equals the sum of its actual uncentered
row actions, for any bounded measurable observable. -/
theorem highUnionSource_bounded_action {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    (Fobs : HighUnionMark E → ℝ) (hF : Measurable Fobs)
    (L : ℝ) (hL : ∀ e, ‖Fobs e‖ ≤ L) :
    (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e
      ∂highUnionLaw R (highCenterMix C)) =
      ∑ i, ∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i) := by
  letI := G.row_probability
  have hi (i : I) : Integrable (R.rowActivation i) (R.rowLaw i) :=
    (integrable_const (R.rowMass i)).mono' (G.activation_measurable i).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun e => by
        simpa only [Real.norm_eq_abs] using G.activation_bound i e))
  have hUi := highRowUnionActivation_integrable R.rowLaw R.rowMass R.rowActivation
    G.activation_measurable hi
  have hUFi := hUi.mul_bdd (hF.comp measurable_inl).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hL (Sum.inl e)))
  rw [highUnionActivation, highUnionLaw, highCenteredRowUnionActivation,
    highCenteredRowUnionLaw, balancedActivation_integral _ _ (highCenterMix_mem C).1
      (highCenterMix_mem C).2.le _
      (highRowUnionActivation_measurable _ _ G.activation_measurable) Fobs hF hUFi]
  exact highRowUnionActivation_action R.rowLaw R.rowMass hpos G.total_positive
    R.rowActivation G.activation_measurable (fun e => Fobs (Sum.inl e))
    (hF.comp measurable_inl) (fun i => (hi i).mul_bdd
      (hF.comp (measurable_inl.comp (rowSigmaMk_measurable i))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun e => hL (Sum.inl ⟨i,e⟩))))

section
variable {d k D M q : ℕ} [NeZero k] [NeZero d] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)

/-- The complete raw reset density is independent of its response atom. -/
theorem finePairSourceRow_reset_density_response_irrel (δ : ℝ)
    (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) (θ : HighRawState d k D) :
    (highUnionRawUpdate (finePairSourceRows C k D M q Cfr T₀ N) δ j
      (Sum.inl ⟨i,e⟩) θ).1 =
    (highUnionRawUpdate (finePairSourceRows C k D M q Cfr T₀ N) δ j
      (Sum.inl ⟨i, finePairRowWithResponse d D M q i r
        (finePairRowDensityProj d D M q i e)⟩) θ).1 := by
  cases i <;> rfl

theorem finePairSourceMass_append_response_irrel
    (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (FinePairRowMark d D M q))) :
    highUnionSourceMass C (finePairSourceRows C k D M q Cfr T₀ N)
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,Sum.inl ⟨i,e⟩)) =
    highUnionSourceMass C (finePairSourceRows C k D M q Cfr T₀ N)
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j
        (h,Sum.inl ⟨i, finePairRowWithResponse d D M q i r
          (finePairRowDensityProj d D M q i e)⟩)) := by
  unfold highUnionSourceMass
  apply integral_congr_ae
  filter_upwards [] with x
  change (highUnionSourceState C _ _).1 x = (highUnionSourceState C _ _).1 x
  rw [highUnionSourceState_append, highUnionSourceState_append]
  exact congrFun (finePairSourceRow_reset_density_response_irrel C Cfr T₀ N _ j i e r _) x


/-- Actual mass indicators are annihilated under canonical append for the
complete unit/coarse/fine source reference. All laws and structural
cancellation identities are derived from the concrete packets. -/
theorem finePairSourceMass_append_indicator_zero
    (hD : 3 ≤ D) (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (hCfr : 1 ≤ Cfr) (hT₀ : 0 < T₀) (hTN : T₀ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (FinePairRowMark d D M q))) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
      (highUnionSourceMass C (finePairSourceRows C k D M q Cfr T₀ N)
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
      highUnionActivation (finePairSourceRows C k D M q Cfr T₀ N) (highCenterMix C) e
      ∂highUnionLaw (finePairSourceRows C k D M q Cfr T₀ N) (highCenterMix C)) = 0 := by
  let R := finePairSourceRows C k D M q Cfr T₀ N
  have G := finePairSourceRows_guards C k D M q hD hq hM Cfr hCfr T₀ N hT₀ hTN
  letI : StandardBorelSpace (HighUnionMark (FinePairRowMark d D M q)) := highUnionMark_standardBorel
  let Fobs : HighUnionMark (FinePairRowMark d D M q) → ℝ := fun e =>
    S.indicator (fun _ : ℝ => (1 : ℝ)) (highUnionSourceMass C R
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)))
  have hF : Measurable Fobs :=
    (measurable_const.indicator hS).comp ((highUnionSourceMass_measurable C R G).comp
      ((historyMarkedAppend_measurable _ _ j).comp (measurable_const.prodMk measurable_id)))
  have hFbound (e) : ‖Fobs e‖ ≤ 1 := by
    exact (norm_indicator_le_norm_self (s := S) (fun _ : ℝ => (1 : ℝ)) _).trans_eq (by simp)
  have hg := highCenterResolution_guards C (M : ℝ) hM
  have hM0 : (0 : ℝ) < M := by linarith [hg.1]
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  have ha : 0 < a := by dsimp [a]; linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  have hab : a < b := by
    dsimp [a,b]
    linarith [hg.2,highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]
  have hCf : 0 < Cfr := by linarith
  have hpos := finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf T₀ N hT₀ hTN
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0, by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  have hrow (i : FinePairRowTag) :
      (∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i)) = 0 := by
    let Fi : FinePairRowDensityMark d D M i → ℝ := fun e =>
      Fobs (Sum.inl ⟨i, finePairRowWithResponse d D M q i r₀ e⟩)
    have hFi : Measurable Fi := hF.comp
      (measurable_inl.comp ((rowSigmaMk_measurable i).comp
        (finePairRowWithResponse_measurable d D M q i r₀)))
    have hFib (e) : ‖Fi e‖ ≤ 1 := hFbound _
    have hfactor (e : FinePairRowMark d D M q i) :
        Fobs (Sum.inl ⟨i,e⟩) = Fi (finePairRowDensityProj d D M q i e) := by
      apply congrArg (S.indicator (fun _ : ℝ => (1 : ℝ)))
      exact finePairSourceMass_append_response_irrel C Cfr T₀ N j i e r₀ h
    calc
      _ = ∫ e, R.rowActivation i e * Fi (finePairRowDensityProj d D M q i e) ∂(R.rowLaw i) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun e => congrArg _ (hfactor e)))
      _ = 0 := finePairRow_density_observable_zero d D M q a b Cfr T₀ N hpos i Fi hFi 1 hFib
  change (∫ e, Fobs e * highUnionActivation R (highCenterMix C) e
    ∂highUnionLaw R (highCenterMix C)) = 0
  calc
    _ = ∫ e, highUnionActivation R (highCenterMix C) e * Fobs e
        ∂highUnionLaw R (highCenterMix C) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun e => mul_comm _ _))
    _ = ∑ i, ∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i) :=
      highUnionSource_bounded_action C R G hpos Fobs hF 1 hFbound
    _ = 0 := by simp only [hrow, Finset.sum_const_zero]

end
end NearlyMinimax
