module

public import NearlyMinimax.FinePairUnionMassAnnihilation


@[expose] public section

/-! Response-coordinate elimination for arbitrary finite complete-row
unions. The structural assumptions concern the uncentered primitive row
packet and its density-mark projection, and are discharged by actual
finite response rules in the concrete source family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- Response-independent raw densities and actual uncentered response
cancellation imply canonical-history mass indicator cancellation for any
finite tagged row union. -/
theorem highUnionSourceMass_append_indicator_zero_of_density_projection
    {d k F : ℕ} [NeZero k] [LinearOrder (HighWindowLabels d k)]
    {I : Type*} [Fintype I] {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    [∀ i, StandardBorelSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    (D : I → Type*) [∀ i, MeasurableSpace (D i)]
    (project : (i : I) → E i → D i) (lift : (i : I) → D i → E i)
    (hlift : ∀ i, Measurable (lift i))
    (hSlope : ∀ j i e x, R.rowSlope j i e x = R.rowSlope j i (lift i (project i e)) x)
    (hIntercept : ∀ i e, R.rowIntercept i e = R.rowIntercept i (lift i (project i e)))
    (hRowZero : ∀ i, ∀ H : D i → ℝ, Measurable H → ∀ L : ℝ,
      (∀ z, ‖H z‖ ≤ L) → (∫ e, R.rowActivation i e * H (project i e) ∂(R.rowLaw i)) = 0)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
      (highUnionSourceMass C R (historyMarkedAppend
        (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
      highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0 := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  let Fobs : HighUnionMark E → ℝ := fun e => S.indicator (fun _ : ℝ => (1 : ℝ))
    (highUnionSourceMass C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)))
  have hF : Measurable Fobs := (measurable_const.indicator hS).comp
    ((highUnionSourceMass_measurable C R G).comp
      ((historyMarkedAppend_measurable _ _ j).comp (measurable_const.prodMk measurable_id)))
  have hFbound (e) : ‖Fobs e‖ ≤ 1 :=
    (norm_indicator_le_norm_self (s := S) (fun _ : ℝ => (1 : ℝ)) _).trans_eq (by simp)
  have hmass (i : I) (e : E i) :
      highUnionSourceMass C R (historyMarkedAppend
        (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,Sum.inl ⟨i,e⟩)) =
      highUnionSourceMass C R (historyMarkedAppend
        (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j
          (h,Sum.inl ⟨i,lift i (project i e)⟩)) := by
    unfold highUnionSourceMass
    apply integral_congr_ae
    filter_upwards [] with x
    change (highUnionSourceState C R _).1 x = (highUnionSourceState C R _).1 x
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if x ∈ highTorusPatch d k j then R.rowSlope j i e x * _ + R.rowIntercept i e else _) =
      (if x ∈ highTorusPatch d k j then R.rowSlope j i (lift i (project i e)) x * _ +
        R.rowIntercept i (lift i (project i e)) else _)
    rw [hSlope j i e x,hIntercept i e]
  have hrow (i : I) : (∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i)) = 0 := by
    let Hi : D i → ℝ := fun z => Fobs (Sum.inl ⟨i,lift i z⟩)
    have hHi : Measurable Hi := hF.comp
      (measurable_inl.comp ((rowSigmaMk_measurable i).comp (hlift i)))
    have hf (e : E i) : Fobs (Sum.inl ⟨i,e⟩) = Hi (project i e) :=
      congrArg (S.indicator (fun _ : ℝ => (1 : ℝ))) (hmass i e)
    calc
      _ = ∫ e, R.rowActivation i e * Hi (project i e) ∂(R.rowLaw i) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun e => congrArg _ (hf e)))
      _ = 0 := hRowZero i Hi hHi 1 (fun z => hFbound _)
  change (∫ e, Fobs e * highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0
  calc
    _ = ∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun e => mul_comm _ _))
    _ = ∑ i, ∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i) :=
      highUnionSource_bounded_action C R G hpos Fobs hF 1 hFbound
    _ = 0 := by simp only [hrow,Finset.sum_const_zero]

end NearlyMinimax
