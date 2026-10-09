module

public import NearlyMinimax.HistoryWordTransport
public import NearlyMinimax.HistoryPriorMeasureIdentity


@[expose] public section

/-!
# True finite mark-law and density transport through heap coordinates
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

variable {J : Type*}

/-- Actual word occurrences and their mark coordinates. -/
def wordHeapPiecePositionEquiv (word : List J) (dependent : J → J → Prop) :
    WordHeapPiece word dependent ≃ Fin word.length where
  toFun := WordHeapPiece.position
  invFun i := ⟨i⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- A true heap isomorphism induces a bijection of actual mark coordinates. -/
def historyHeapCoordinateEquiv {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) : Fin u.length ≃ Fin v.length :=
  (wordHeapPiecePositionEquiv u dependent).symm.trans
    (e.toEquiv.trans (wordHeapPiecePositionEquiv v dependent))

@[simp] theorem historyHeapCoordinateEquiv_position {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) (x : WordHeapPiece u dependent) :
    historyHeapCoordinateEquiv e x.position = (e x).position := by
  cases x
  rfl

/-- This is the actual measurable coordinate insertion into another word representative. -/
def historyHeapMarkEquiv {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E] :
    (Fin u.length → E) ≃ᵐ (Fin v.length → E) :=
  MeasurableEquiv.piCongrLeft (fun _ => E) (historyHeapCoordinateEquiv e)

@[simp] theorem historyHeapMarkEquiv_position {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E]
    (marks : Fin u.length → E) (x : WordHeapPiece u dependent) :
    historyHeapMarkEquiv e marks (e x).position = marks x.position := by
  have hh := MeasurableEquiv.piCongrLeft_apply_apply (historyHeapCoordinateEquiv e)
    (β := fun _ : Fin v.length => E) marks x.position
  simpa only [historyHeapMarkEquiv, historyHeapCoordinateEquiv_position] using hh

/-- The actual independent product mark laws are transported exactly. -/
theorem historyHeapMarkEquiv_preserving {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyHeapMarkEquiv e (E := E))
      (Measure.pi (fun _ : Fin u.length => π)) (Measure.pi (fun _ : Fin v.length => π)) :=
  measurePreserving_piCongrLeft (fun _ : Fin v.length => π) (historyHeapCoordinateEquiv e)

/-- The actual polynomial evaluated at an arbitrary marked word representative. -/
def historyWordMarkedDensity (word : List J) (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (marks : Fin word.length → E) : ℝ :=
  historyScaledUpperDensity (fun x : WordHeapPiece word dependent => a (marks x.position)) ρ Finset.univ t

theorem historyWordMarkedDensity_measurable (word : List J) (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) :
    Measurable (historyWordMarkedDensity word dependent ρ t a) := by
  classical
  unfold historyWordMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  apply Finset.measurable_fun_sum _
  intro P hP
  apply Measurable.const_mul
  apply Finset.measurable_fun_prod _
  intro x hx
  exact ha.comp (measurable_pi_apply x.position)

/-- The genuine polynomial density transports under the actual coordinate map. -/
theorem historyHeapMarkEquiv_density {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E]
    (a : E → ℝ) (marks : Fin u.length → E) (ρ t : ℝ) :
    historyWordMarkedDensity v dependent ρ t a (historyHeapMarkEquiv e marks) =
      historyWordMarkedDensity u dependent ρ t a marks := by
  have hw : (fun x : WordHeapPiece v dependent => a (historyHeapMarkEquiv e marks x.position)) ∘ e =
      (fun x : WordHeapPiece u dependent => a (marks x.position)) := by
    funext x
    exact congrArg a (historyHeapMarkEquiv_position e marks x)
  have ht := historyScaledUpperDensity_orderIso_map e
    (fun x : WordHeapPiece v dependent => a (historyHeapMarkEquiv e marks x.position)) ρ Finset.univ t
  rw [Finset.map_univ_equiv e.toEquiv, hw] at ht
  exact ht

/-- Actual conditional positive mark laws are independent of the representative word. -/
theorem historyHeapMarkEquiv_withDensity {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a) (ρ t : ℝ) :
    Measure.map (historyHeapMarkEquiv e)
      ((Measure.pi (fun _ : Fin u.length => π)).withDensity
        (fun marks => ENNReal.ofReal (historyWordMarkedDensity u dependent ρ t a marks))) =
      (Measure.pi (fun _ : Fin v.length => π)).withDensity
        (fun marks => ENNReal.ofReal (historyWordMarkedDensity v dependent ρ t a marks)) := by
  let p : (Fin v.length → E) → ℝ≥0∞ := fun marks =>
    ENNReal.ofReal (historyWordMarkedDensity v dependent ρ t a marks)
  have hp : Measurable p := (historyWordMarkedDensity_measurable v dependent ρ t a ha).ennreal_ofReal
  have hd : (fun marks => ENNReal.ofReal (historyWordMarkedDensity u dependent ρ t a marks)) =
      p ∘ historyHeapMarkEquiv e := by
    funext marks
    exact congrArg ENNReal.ofReal (historyHeapMarkEquiv_density e a marks ρ t).symm
  rw [hd, historyMap_withDensity _ _ (historyHeapMarkEquiv e).measurable p hp,
    (historyHeapMarkEquiv_preserving e π).map_eq]

end NearlyMinimax
