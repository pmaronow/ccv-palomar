module

public import NearlyMinimax.HighUnionInvariantMass


@[expose] public section

/-! The actual complete-row mass-power tilt is a probability measure;
the source bounded-differences MGF gives its exceptional mass probability. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Generic
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k F I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionSourceMass_coarse_interval
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    highUnionSourceMass C R h ∈ Icc C.densityLower C.densityUpper := by
  have hg := highCenterResolution_guards C M G.resolution
  have hM0 : 0 < M := by linarith [hg.1]
  have hb := highUnionSourceMass_interval C R G h
  constructor
  · exact (le_add_of_nonneg_right (one_div_pos.mpr hM0).le).trans hb.1
  · exact hb.2.trans (sub_le_self _ (one_div_pos.mpr hM0).le)

/-- Genuine complete-union source positivity implies its true mass-power
prior remains a probability experiment at every source time. -/
theorem highUnionSourceTiltedPrior_probability (hpos : ∀ i, 0 < R.rowMass i)
    (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass R.rowMass/highCenterMix C)/historyReferenceRho (3^d) ≤
      1/(2+8*((3^d:ℕ):ℝ)^2)) (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C)))
      (highUnionSourceMass C R) n) := by
  letI := highUnionSourcePrior_probability C R G hpos T hT hsmall t ht
  exact massPowerTilt_isProbability _ _ (highUnionSourceMass_measurable C R G) n
    C.densityLower C.densityUpper C.densityLower_pos (highUnionSourceMass_coarse_interval C R G)

/-- Actual complete-union reference fiber means and true torus block
oscillation yield the mass-tilted exceptional probability. -/
theorem highUnionSourceMass_reference_tilted_tail (hk : 2 ≤ k) (n : ℕ) (ε : ℝ)
    (hε : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ ε) :
    (massPowerTilt
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) (highUnionSourceMass C R) n).real
      {h | ε < |highUnionSourceMass C R h-1|} ≤
      2*Real.exp (-ε^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  letI := highUnionSourceLaw_probability C R G
  letI := historyMarkedReference_probability _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C))
  exact massPowerTilt_abs_tail _ _ (highUnionSourceMass_measurable C R G) n
    C.densityLower C.densityUpper C.densityLower_pos (highUnionSourceMass_coarse_interval C R G)
    (highUnionSourceMass_reference_mean_one C R G) _ ε
    (highHistoryMassParameter_pos d k _ _ (by omega)
      (C.densityLower_lt_one.trans C.one_lt_densityUpper))
    (highUnionSourceMass_reference_mgf C R G hk) hε

end Generic

section ActualFinePair
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (hCfr : 1 ≤ Cfr) (hT₀ : 0 < T₀) (hTN : T₀ < N)
include hD hq hM hCfr hT₀ hTN

/-- Every actual unit/coarse/fine prior time has the true tilted
exceptional mass tail. Mass-law invariance follows from the actual
response-summed packets and is not a premise. -/
theorem finePairSourceMass_prior_tilted_tail (hk : 2 ≤ k) (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (finePairSourceRows C k D M q Cfr T₀ N).rowMass /
      highCenterMix C) / historyReferenceRho (3^d) ≤ 1 / (2+8*((3^d:ℕ):ℝ)^2))
    (n : ℕ) (ε : ℝ)
    (hε : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ ε)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw (finePairSourceRows C k D M q Cfr T₀ N) (highCenterMix C))
        (highUnionActivation (finePairSourceRows C k D M q Cfr T₀ N) (highCenterMix C)))
      (highUnionSourceMass C (finePairSourceRows C k D M q Cfr T₀ N)) n).real
      {h | ε < |highUnionSourceMass C (finePairSourceRows C k D M q Cfr T₀ N) h-1|} ≤
      2*Real.exp (-ε^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  have G := finePairSourceRows_guards C k D M q hD hq hM Cfr hCfr T₀ N hT₀ hTN
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _
    (highUnionSourceMass_measurable C _ G) n
    (finePairSourceMass_prior_law C Cfr T₀ N hD hq hM hCfr hT₀ hTN T hT hsmall t ht) ε]
  exact highUnionSourceMass_reference_tilted_tail C _ G hk n ε hε

end ActualFinePair
end NearlyMinimax
