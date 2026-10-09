module

public import NearlyMinimax.HistoryReferenceMeasure


@[expose] public section

/-!
# Actual shape append and its reference-weight change

Appending a fixed label descends through independent exchanges, is injective
by the proved dependent-pair characterization, increases length by exactly one,
and multiplies the exact source reference weight by `rho`.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

omit [Fintype J] [LinearOrder J] in
/-- Independent-exchange equivalence is preserved by an arbitrary suffix. -/
theorem historyShapeRelation_append {independent : J → J → Prop} {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) (suffix : List J) :
    Relation.EqvGen (IndependentHistoryExchange independent) (u ++ suffix) (v ++ suffix) := by
  induction h with
  | rel u v h =>
    cases h with
    | swap before after x y hxy =>
      simpa only [List.append_assoc, List.cons_append] using
        Relation.EqvGen.rel _ _ (IndependentHistoryExchange.swap before (after ++ suffix) x y hxy)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Appending an actual local-update label is well-defined on the history shape. -/
def historyShapeAppend (dependent : J → J → Prop) (j : J) :
    HistoryShape (fun a b => ¬ dependent a b) → HistoryShape (fun a b => ¬ dependent a b) :=
  Quotient.lift (fun word => Quotient.mk _ (word ++ [j]))
    (fun _ _ h => Quotient.sound (historyShapeRelation_append h [j]))

omit [Fintype J] [LinearOrder J] in
@[simp] theorem historyShapeAppend_mk (dependent : J → J → Prop) (j : J) (word : List J) :
    historyShapeAppend dependent j (Quotient.mk _ word) = Quotient.mk _ (word ++ [j]) := rfl

omit [Fintype J] in
/-- The append map cannot merge histories: dependent pair words right-cancel. -/
theorem historyShapeAppend_injective (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (j : J) :
    Function.Injective (historyShapeAppend dependent j) := by
  intro g h heq
  induction g using Quotient.inductionOn
  rename_i u
  induction h using Quotient.inductionOn
  rename_i v
  apply Quotient.sound
  apply historyShapeRelation_of_pair_projections hrefl hsymm
  intro i k hik
  have hc := congrArg (fun shape => historyShapePairCode dependent hrefl hsymm shape ⟨(i, k), hik⟩) heq
  change historyPairProjection i k (u ++ [j]) = historyPairProjection i k (v ++ [j]) at hc
  unfold historyPairProjection at hc ⊢
  rw [List.filter_append, List.filter_append] at hc
  exact List.append_cancel_right hc

omit [Fintype J] in
@[simp] theorem historyShapeMultiplicity_append (dependent : J → J → Prop) (j i : J)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeMultiplicity dependent i (historyShapeAppend dependent j g) =
      historyShapeMultiplicity dependent i g + if j = i then 1 else 0 := by
  induction g using Quotient.inductionOn
  rename_i word
  change (word ++ [j]).count i = word.count i + if j = i then 1 else 0
  by_cases hj : j = i
  · subst j; simp
  · simp [hj]

@[simp] theorem historyShapeLength_append (dependent : J → J → Prop) (j : J)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeLength dependent (historyShapeAppend dependent j g) = historyShapeLength dependent g + 1 := by
  induction g using Quotient.inductionOn
  rename_i word
  rw [historyShapeAppend_mk, historyShapeLength_mk, historyShapeLength_mk]
  simp

/-- The exact source reference factor needed for append/delete change of variables. -/
theorem historyShapeReferenceWeight_append (dependent : J → J → Prop) (Δ : ℕ) (j : J)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeReferenceWeight dependent Δ (historyShapeAppend dependent j g) =
      historyReferenceRho Δ * historyShapeReferenceWeight dependent Δ g := by
  unfold historyShapeReferenceWeight
  rw [historyShapeLength_append, pow_succ, mul_comm]

/-- Histories which terminate in a specified maximal update label. -/
abbrev HistoryTerminalShape (dependent : J → J → Prop) (j : J) :=
  Set.range (historyShapeAppend dependent j)

omit [Fintype J] [LinearOrder J] in
/-- A measurable append map on the countable shape space. -/
theorem historyShapeAppend_measurable (dependent : J → J → Prop) (j : J) :
    Measurable (historyShapeAppend dependent j) := measurable_from_top

end NearlyMinimax
