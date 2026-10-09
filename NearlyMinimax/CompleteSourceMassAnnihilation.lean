module

public import NearlyMinimax.CompleteSourceRows
public import NearlyMinimax.HighUnionDensityCancellation


@[expose] public section

/-! Actual canonical mass cancellation for the entire source packet,
including the singleton, all three pair rows, and every selected higher
coarse/fine row. Primitive cancellation is proved from finite response
atoms on the true carrier spaces. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

abbrev SourceRowDensityMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowDensityMark d D M p
  | .inr (.inl _) => Unit × HighDensityMarkIndex D 1 D
  | .inr (.inr i) => HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2 ×
      HighDensityMarkIndex (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D

instance sourceRowDensityMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (SourceRowDensityMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => infer_instance
  | inr i => cases i <;> dsimp [SourceRowDensityMark] <;> infer_instance

def sourceRowDensityProj (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowMark d D M q a b C lam ℓ N μ i → SourceRowDensityMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowDensityProj d D M q p
  | .inr (.inl _) => fun e => (e.1,e.2.1)
  | .inr (.inr _) => fun e => (e.1,e.2.1)

def sourceRowDensityLift (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowDensityMark d D M q a b C lam ℓ N μ i → SourceRowMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowWithResponse d D M q p r
  | .inr (.inl _) => fun e => (e.1,(e.2,r))
  | .inr (.inr _) => fun e => (e.1,(e.2,r))

theorem sourceRowDensityLift_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    Measurable (sourceRowDensityLift d D M q a b C lam ℓ N μ r i) := by
  cases i with
  | inl p => exact finePairRowWithResponse_measurable d D M q p r
  | inr i => cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

theorem sourceRow_density_projection_slope (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) (j : HighWindowLabels d k)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (e : SourceRowMark d D M q a b C lam ℓ N μ i) (x : Covariate d) :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i e x =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i
      (sourceRowDensityLift d D M q a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) x := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

theorem sourceRow_density_projection_intercept (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (e : SourceRowMark d D M q a b C lam ℓ N μ i) :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i e =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i
      (sourceRowDensityLift d D M q a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

theorem sourceRow_density_observable_zero (d : ℕ) [NeZero d] (k D M q : ℕ)
    (a b C lam ℓ N μ : ℝ)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (H : SourceRowDensityMark d D M q a b C lam ℓ N μ i → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : ∀ z, ‖H z‖ ≤ B) :
    (∫ e, (sourceRowData d k D M q a b C lam ℓ N μ).rowActivation i e *
      H (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)
      ∂(sourceRowData d k D M q a b C lam ℓ N μ).rowLaw i) = 0 := by
  cases i with
  | inl p =>
    exact finePairRow_density_observable_zero d D M q a b C ℓ N
      (fun p => hpos (Sum.inl p)) p H hH B hB
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacketAbsoluteLaw_density_observable_zero (Measure.dirac ()) a b D 1 D q C
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inr (.inl ()))) H hH B hB
    | inr i =>
      exact higherBandRow_density_observable_zero d (higherBandFamilyTarget i.val)
        (higherBandFamilyGuardDegree M i.val) D q a b C lam ℓ
        (higherBandFamilyUpper d ℓ N μ i.val) i.val.2 i.property.1
        (hpos (.inr (.inr i))) H hH B hB

theorem sourceRowMass_positive_actual (d : ℕ) [NeZero d] (k D M q : ℕ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (C : ℝ) (hC : 0 < C) (lam ℓ N μ : ℝ) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p => exact finePairRowMass_positive d D hD M q hq a b ha hab C hC ℓ N hℓ hℓN p
  | inr i =>
    cases i with
    | inl _ => exact singletonRowMass_positive d D q hq a b ha hab C hC
    | inr i => exact higherBandFamily_mass_positive d k D M q a b C lam ℓ N μ i

/-- Genuine canonical append annihilation for the complete actual source
family, with only the original construction's numerical guards. -/
theorem completeSourceMass_append_indicator_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ))) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ)
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
      highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C) e
      ∂highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)) = 0 := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hCf : 0 < Cfr := by linarith
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr hCf lam ℓ N μ hℓ hℓN
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  exact highUnionSourceMass_append_indicator_zero_of_density_projection C R
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) hpos
    (SourceRowDensityMark d D M q a b Cfr lam ℓ N μ)
    (sourceRowDensityProj d D M q a b Cfr lam ℓ N μ)
    (sourceRowDensityLift d D M q a b Cfr lam ℓ N μ r₀)
    (sourceRowDensityLift_measurable d D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_slope d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_intercept d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_observable_zero d k D M q a b Cfr lam ℓ N μ hpos) j h S hS

end NearlyMinimax
