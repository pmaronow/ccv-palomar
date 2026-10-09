module

public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighUnionScorePrimitives


@[expose] public section

/-! Actual response-coordinate elimination makes every appended density
product annihilate under the full source activation, at every sample count. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

 theorem highUnionSourceResetDensity_product_zero_of_density_projection
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
    (n : ℕ) (x : Fin n → Covariate d) :
    (∫ e, highUnionActivation R (highCenterMix C) e *
      ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0 := by
  let Fobs : HighUnionMark E → ℝ := fun e => ∏ i, highUnionSourceResetDensity C R j h e (x i)
  have hF : Measurable Fobs := Finset.measurable_fun_prod _ (fun i _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp (measurable_id.prodMk measurable_const))
  have hFb (e : HighUnionMark E) : ‖Fobs e‖ ≤ C.densityUpper^n := by
    simpa only [Real.norm_eq_abs,Fobs] using finite_density_product_abs_bound
      (fun i => highUnionSourceResetDensity C R j h e (x i)) C.densityUpper
      (by linarith [C.one_lt_densityUpper])
      (fun i => highUnionSourceResetDensity_abs_le C R G j h e (x i))
  have hp (i : I) (e : E i) (z : Covariate d) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) z =
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,lift i (project i e)⟩) z := by
    unfold highUnionSourceResetDensity highUnionSourceDensity
    change (highUnionSourceState C R _).1 z = (highUnionSourceState C R _).1 z
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if z ∈ highTorusPatch d k j then R.rowSlope j i e z * _ + R.rowIntercept i e else _) =
      (if z ∈ highTorusPatch d k j then R.rowSlope j i (lift i (project i e)) z * _ +
        R.rowIntercept i (lift i (project i e)) else _)
    rw [hSlope j i e z,hIntercept i e]
  have hrow (i : I) : (∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i)) = 0 := by
    let Hi : D i → ℝ := fun z => Fobs (Sum.inl ⟨i,lift i z⟩)
    have hHi : Measurable Hi := hF.comp
      (measurable_inl.comp ((rowSigmaMk_measurable i).comp (hlift i)))
    have he (e : E i) : Fobs (Sum.inl ⟨i,e⟩) = Hi (project i e) := by
      apply Finset.prod_congr rfl
      intro l _
      exact hp i e (x l)
    calc
      _ = ∫ e, R.rowActivation i e * Hi (project i e) ∂(R.rowLaw i) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun e => congrArg _ (he e)))
      _ = 0 := hRowZero i Hi hHi (C.densityUpper^n) (fun z => hFb _)
  change (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C)) = 0
  rw [highUnionSource_bounded_action C R G hpos Fobs hF (C.densityUpper^n) hFb]
  simp only [hrow,Finset.sum_const_zero]

/-- Complete actual singleton, pair, and higher coarse/fine rows have
conditional density-product zero mass at every count. -/
theorem completeSourceDensity_product_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ))) (n : ℕ) (x : Fin n → Covariate d) :
    (∫ e, highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C) e *
      ∏ i, highUnionSourceResetDensity C (completeSourceRows C k D M q Cfr lam ℓ N μ)
        j h e (x i) ∂highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)) = 0 := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr
    (by linarith) lam ℓ N μ hℓ hℓN
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  exact highUnionSourceResetDensity_product_zero_of_density_projection C R
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) hpos
    (SourceRowDensityMark d D M q a b Cfr lam ℓ N μ)
    (sourceRowDensityProj d D M q a b Cfr lam ℓ N μ)
    (sourceRowDensityLift d D M q a b Cfr lam ℓ N μ r₀)
    (sourceRowDensityLift_measurable d D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_slope d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_intercept d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_observable_zero d k D M q a b Cfr lam ℓ N μ hpos) j h n x

end NearlyMinimax
