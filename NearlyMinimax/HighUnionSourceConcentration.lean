module

public import NearlyMinimax.HighUnionSource
public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.HighHistoryInvariantMass


@[expose] public section

/-! The true complete-union canonical mass has mean one and the exact
source grid concentration parameter under the infinite reference law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
  [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)
  {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionSourceMass_reference_mean_one :
    (∫ h, highUnionSourceMass C R h
      ∂historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) = 1 := by
  letI := highUnionSourceLaw_probability C R G
  apply historyMarkedReference_mean_one (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (3^d) (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C)) (highUnionSourceMass C R)
    (highUnionSourceMass_measurable C R G) C.densityUpper _
    (highUnionSourceMass_fiber_mean_one C R G)
  intro h
  have hp := highUnionSourceMass_interval C R G h
  have hM0 : 0 < M := by
    have := (highCenterResolution_guards C M G.resolution).1
    linarith
  rw [abs_of_nonneg (by linarith [hp.1, C.densityLower_pos, one_div_pos.mpr hM0])]
  linarith [hp.2, one_div_pos.mpr hM0]

theorem highUnionSourceMass_reference_mgf (hk : 2 ≤ k) (u : ℝ) :
    (∫ h, Real.exp (u * (highUnionSourceMass C R h-1))
      ∂historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) ≤
      Real.exp (highHistoryMassParameter d k C.densityLower C.densityUpper * u^2) := by
  letI := highUnionSourceLaw_probability C R G
  have hm := highUnionSourceMass_measurable C R G
  have hBound : ∀ h, |highUnionSourceMass C R h| ≤ C.densityUpper := by
    intro h
    have hp := highUnionSourceMass_interval C R G h
    have hM0 : 0 < M := by
      have := (highCenterResolution_guards C M G.resolution).1
      linarith
    rw [abs_of_nonneg (by linarith [hp.1, C.densityLower_pos, one_div_pos.mpr hM0])]
    linarith [hp.2, one_div_pos.mpr hM0]
  have hgap : 0 ≤ C.densityUpper-C.densityLower := by
    linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have h := historyMarkedReference_mass_mgf (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (3^d) (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C)) (highUnionSourceMass C R) hm C.densityUpper
    ((2 / (k : ℝ))^d * (C.densityUpper-C.densityLower)) (by positivity)
    hBound (highUnionSourceMass_fiber_mean_one C R G)
    (fun g j marks marks' hMarks => highUnionSourceMass_block_oscillation C R G hk g marks marks' j hMarks) u
  convert h using 1
  congr 1
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
  unfold highHistoryMassParameter
  ring

end
end NearlyMinimax
