module

public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighUnionInvariantMass


@[expose] public section

/-! The complete singleton, pair, and higher coarse/fine packet source
has a genuine time-independent raw mass law. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
include hD hq hM hCfr hℓ hℓN

theorem completeSourceRows_mass_positive (i : SourceRowIndex d D M q
    (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ) :
    0 < (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass i := by
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  exact sourceRowMass_positive_actual d k D M q hD hq _ _ ha hab Cfr
    (by linarith) lam ℓ N μ hℓ hℓN i

/-- Probability of the actual full source path follows from its primitive
finite packet guards and the explicit history positivity budget. -/
theorem completeSourcePrior_probability (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3^d) ≤ 1 / (2+8*((3^d : ℕ):ℝ)^2))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
      (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
      (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) :=
  highUnionSourcePrior_probability C _
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    (completeSourceRows_mass_positive C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) T hT hsmall t ht

/-- Actual canonical append cancellation closes mass-law invariance for
all retained rows, including every higher coarse/fine target. -/
theorem completeSourceMass_prior_law (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3^d) ≤ 1 / (2+8*((3^d : ℕ):ℝ)^2))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) =
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) :=
  highUnionSourceMass_prior_law_of_append_annihilation C _
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    (completeSourceRows_mass_positive C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    T hT hsmall
    (completeSourceMass_append_indicator_zero C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) t ht

end NearlyMinimax
