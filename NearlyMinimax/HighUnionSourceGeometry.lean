module

public import NearlyMinimax.HighUnionSource


@[expose] public section

/-! Exact locality of the complete-row canonical source reset. -/
noncomputable section
open Set MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)]
  (R : HighUnionRowData d k F I E)

theorem highUnionRawUpdate_density_of_not_mem (δ : ℝ)
    (j : HighWindowLabels d k) (e : HighUnionMark E) (θ : HighRawState d k F)
    (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    (highUnionRawUpdate R δ j e θ).1 x = θ.1 x := by
  simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_right hx]

theorem highUnionRawUpdate_density_of_mem (δ : ℝ)
    (j : HighWindowLabels d k) (e : HighUnionMark E) (θ : HighRawState d k F)
    (x : Covariate d) (hx : x ∈ highTorusPatch d k j) :
    (highUnionRawUpdate R δ j e θ).1 x =
      highUnionSlope R j e x * θ.1 x + highUnionIntercept R δ e := by
  simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_left hx]

variable [NeZero k] [LinearOrder (HighWindowLabels d k)] (C : ModelConstants d)

theorem highUnionSourceState_append (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) :
    highUnionSourceState C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) =
    highUnionRawUpdate R (highCenterMix C) j e (highUnionSourceState C R h) :=
  highUnionMarkedState_append R _ highUnionVacuum j h e

/-- Appending a full source mark leaves every density value outside that
label's physical patch exactly unchanged. -/
theorem highUnionSourceDensity_append_of_not_mem (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    highUnionSourceDensity C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) x =
    highUnionSourceDensity C R h x := by
  change (highUnionSourceState C R _).1 x = _
  rw [highUnionSourceState_append R C j h e]
  exact highUnionRawUpdate_density_of_not_mem R _ j e _ x hx

end
end NearlyMinimax
