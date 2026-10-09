module

public import Mathlib


@[expose] public section

/-!
# Finite history shapes and well-defined local state updates

Shapes are quotients of finite piece words by exchanges of consecutive
independent pieces. The state obtained by applying the marked updates descends
to this quotient. Commutativity of disjoint pointwise-affine patch updates and
separate response-coordinate updates is proved concretely.
-/

noncomputable section
namespace NearlyMinimax

inductive IndependentHistoryExchange {α : Type*} (independent : α → α → Prop) : List α → List α → Prop
  | swap (before after : List α) (x y : α) (hxy : independent x y) :
      IndependentHistoryExchange independent (before ++ x :: y :: after) (before ++ y :: x :: after)

def historyShapeSetoid {α : Type*} (independent : α → α → Prop) : Setoid (List α) where
  r := Relation.EqvGen (IndependentHistoryExchange independent)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

def HistoryShape {α : Type*} (independent : α → α → Prop) := Quotient (historyShapeSetoid independent)

def historyWordState {α X : Type*} (update : α → X → X) (initial : X) (word : List α) : X :=
  word.foldl (fun state piece => update piece state) initial

theorem historyWordState_exchange {α X : Type*} {independent : α → α → Prop}
    {update : α → X → X}
    (hcomm : ∀ x y, independent x y → ∀ state, update y (update x state) = update x (update y state))
    (initial : X) {word word' : List α} (h : IndependentHistoryExchange independent word word') :
    historyWordState update initial word = historyWordState update initial word' := by
  cases h with
  | swap before after x y hxy =>
    unfold historyWordState
    simp only [List.foldl_append, List.foldl_cons]
    rw [hcomm x y hxy]

theorem historyWordState_shape_invariant {α X : Type*} {independent : α → α → Prop}
    {update : α → X → X}
    (hcomm : ∀ x y, independent x y → ∀ state, update y (update x state) = update x (update y state))
    (initial : X) {word word' : List α}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) word word') :
    historyWordState update initial word = historyWordState update initial word' := by
  induction h with
  | rel _ _ h => exact historyWordState_exchange hcomm initial h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def historyShapeState {α X : Type*} {independent : α → α → Prop}
    (update : α → X → X)
    (hcomm : ∀ x y, independent x y → ∀ state, update y (update x state) = update x (update y state))
    (initial : X) : HistoryShape independent → X :=
  Quotient.lift (historyWordState update initial) (fun _ _ h => historyWordState_shape_invariant hcomm initial h)

theorem historyShapeState_mk {α X : Type*} {independent : α → α → Prop}
    (update : α → X → X)
    (hcomm : ∀ x y, independent x y → ∀ state, update y (update x state) = update x (update y state))
    (initial : X) (word : List α) :
    historyShapeState update hcomm initial (Quotient.mk (historyShapeSetoid independent) word) =
      historyWordState update initial word := rfl

instance historyShape_countable {α : Type*} [Countable α] (independent : α → α → Prop) :
    Countable (HistoryShape independent) := by
  unfold HistoryShape
  infer_instance

def affinePatchUpdate {X : Type*} (patch : Set X) (A B : X → ℝ) (state : X → ℝ) : X → ℝ := by
  classical
  exact fun x => if x ∈ patch then A x * state x + B x else state x

theorem affinePatchUpdate_commute {X : Type*} (P Q : Set X)
    (A B C D : X → ℝ) (hPQ : Disjoint P Q) (state : X → ℝ) :
    affinePatchUpdate Q C D (affinePatchUpdate P A B state) =
      affinePatchUpdate P A B (affinePatchUpdate Q C D state) := by
  classical
  funext x
  by_cases hxP : x ∈ P
  · have hxQ : x ∉ Q := fun hxQ => Set.disjoint_left.1 hPQ hxP hxQ
    simp [affinePatchUpdate, hxP, hxQ]
  · by_cases hxQ : x ∈ Q <;> simp [affinePatchUpdate, hxP, hxQ]

def responseCoordinateUpdate {α E : Type*} [DecidableEq α]
    (j : α) (response : E → E) (state : α → E) : α → E := Function.update state j (response (state j))

theorem responseCoordinateUpdate_commute {α E : Type*} [DecidableEq α]
    {i j : α} (hij : i ≠ j) (f g : E → E) (state : α → E) :
    responseCoordinateUpdate j g (responseCoordinateUpdate i f state) =
      responseCoordinateUpdate i f (responseCoordinateUpdate j g state) := by
  unfold responseCoordinateUpdate
  simp only [Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ state

def rawPatchUpdate {α X E : Type*} [DecidableEq α] (j : α) (patch : Set X)
    (A B : X → ℝ) (response : E → E) (state : (X → ℝ) × (α → E)) : (X → ℝ) × (α → E) :=
  (affinePatchUpdate patch A B state.1, responseCoordinateUpdate j response state.2)

/-- The actual density/response patch updates commute at disjoint, distinct labels. -/
theorem rawPatchUpdate_commute {α X E : Type*} [DecidableEq α] {i j : α}
    (P Q : Set X) (A B C D : X → ℝ) (f g : E → E)
    (hij : i ≠ j) (hPQ : Disjoint P Q) (state : (X → ℝ) × (α → E)) :
    rawPatchUpdate j Q C D g (rawPatchUpdate i P A B f state) =
      rawPatchUpdate i P A B f (rawPatchUpdate j Q C D g state) := by
  exact Prod.ext (affinePatchUpdate_commute P Q A B C D hPQ state.1)
    (responseCoordinateUpdate_commute hij f g state.2)

end NearlyMinimax
