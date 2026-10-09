module

public import NearlyMinimax.HistoryMarkedStateAppend
public import NearlyMinimax.HighWindowGeometry


@[expose] public section

/-! Canonical append for genuine mark-dependent patch resets. Slopes and
intercepts may depend on the entire source mark, including its spatial mark. -/
noncomputable section
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedRawState_patch_append {Z E R : Type*} [DecidableEq J] [MeasurableSpace E]
    (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (patch : J → Set Z) (slope intercept : J → E → Z → ℝ)
    (response : J → E → R → R)
    (hdistinct : ∀ i j, ¬ dependent i j → i ≠ j)
    (hdisjoint : ∀ i j, ¬ dependent i j → Disjoint (patch i) (patch j))
    (initial : (Z → ℝ) × (J → R)) (j : J) (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedRawState dependent
      (fun j e => rawPatchUpdate j (patch j) (slope j e) (intercept j e) (response j e)) initial
      (historyMarkedAppend dependent hsymm j (h, fresh)) =
    rawPatchUpdate j (patch j) (slope j fresh) (intercept j fresh) (response j fresh)
      (historyMarkedRawState dependent
        (fun j e => rawPatchUpdate j (patch j) (slope j e) (intercept j e) (response j e)) initial h) := by
  apply historyMarkedRawState_append
  intro i j h e f state
  exact rawPatchUpdate_commute _ _ _ _ _ _ _ _ (hdistinct i j h) (hdisjoint i j h) state

theorem historyMarkedRawState_affinePatch_append {Z E : Type*} [MeasurableSpace E]
    (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (patch : J → Set Z) (slope intercept : J → E → Z → ℝ)
    (hdisjoint : ∀ i j, ¬ dependent i j → Disjoint (patch i) (patch j))
    (initial : Z → ℝ) (j : J) (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedRawState dependent
      (fun j e => affinePatchUpdate (patch j) (slope j e) (intercept j e)) initial
      (historyMarkedAppend dependent hsymm j (h, fresh)) =
    affinePatchUpdate (patch j) (slope j fresh) (intercept j fresh)
      (historyMarkedRawState dependent
        (fun j e => affinePatchUpdate (patch j) (slope j e) (intercept j e)) initial h) := by
  apply historyMarkedRawState_append
  intro i j h e f state
  exact affinePatchUpdate_commute _ _ _ _ _ _ (hdisjoint i j h) state

/-- The torus-neighbour dependency gives canonical append compatibility
for arbitrary full-mark density and coefficient resets. -/
theorem highMarkedRawState_patch_append (d k : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    {E R : Type*} [MeasurableSpace E]
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (response : HighWindowLabels d k → E → R → R)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → R))
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) E) (fresh : E) :
    historyMarkedRawState (fun i j => j ∈ highNeighborLabels d k i)
      (fun j e => rawPatchUpdate j (highTorusPatch d k j) (slope j e) (intercept j e) (response j e)) initial
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, fresh)) =
    rawPatchUpdate j (highTorusPatch d k j) (slope j fresh) (intercept j fresh) (response j fresh)
      (historyMarkedRawState (fun i j => j ∈ highNeighborLabels d k i)
        (fun j e => rawPatchUpdate j (highTorusPatch d k j) (slope j e) (intercept j e) (response j e)) initial h) := by
  have hi : ∀ i j : HighWindowLabels d k, j ∉ highNeighborLabels d k i → i ≠ j := by
    intro i j h he
    subst j
    exact h (highNeighborLabels_self_mem d k i)
  have hd : ∀ i j : HighWindowLabels d k, j ∉ highNeighborLabels d k i →
      Disjoint (highTorusPatch d k i) (highTorusPatch d k j) :=
    fun i j h => highTorusPatch_disjoint_of_not_neighbor d k i j h
  exact historyMarkedRawState_patch_append
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (highTorusPatch d k) slope intercept response hi hd initial j h fresh

end NearlyMinimax
