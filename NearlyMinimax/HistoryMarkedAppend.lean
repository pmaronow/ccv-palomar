module

public import NearlyMinimax.HistoryCoordinateTransport
public import NearlyMinimax.HistoryShapeChangeVariables


@[expose] public section

/-!
# Actual independent mark insertion and canonical append coordinates
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

omit [Fintype J] [LinearOrder J] in
/-- The canonical appended word carries the same actual labelled dependency heap. -/
theorem historyCanonicalAppendHeapIso_exists (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    ∃ e : WordHeapPiece (g.out ++ [j]) dependent ≃o
        WordHeapPiece (historyShapeAppend dependent j g).out dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  have hmk : (Quotient.mk _ (g.out ++ [j]) : HistoryShape (fun a b => ¬ dependent a b)) =
      historyShapeAppend dependent j g := by
    exact congrArg (historyShapeAppend dependent j) (Quotient.out_eq g)
  have hr : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b))
      (g.out ++ [j]) (historyShapeAppend dependent j g).out :=
    Quotient.exact (hmk.trans (Quotient.out_eq _).symm)
  exact historyShapeRelation_heapIso dependent hsymm hr

/-- Choose once an actual representative coordinate transport, not a law or score bound. -/
def historyCanonicalAppendHeapIso (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    WordHeapPiece (g.out ++ [j]) dependent ≃o
      WordHeapPiece (historyShapeAppend dependent j g).out dependent :=
  (historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose

omit [Fintype J] [LinearOrder J] in
theorem historyCanonicalAppendHeapIso_label (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) (x : WordHeapPiece (g.out ++ [j]) dependent) :
    wordHeapLabel (historyCanonicalAppendHeapIso dependent hsymm j g x) = wordHeapLabel x :=
  (historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose_spec x

/-- Insert one genuinely independent mark at the last finite coordinate. -/
def historyFiniteMarkAppendEquiv (n : ℕ) {E : Type*} [MeasurableSpace E] :
    E × (Fin n → E) ≃ᵐ (Fin (n + 1) → E) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).symm

theorem historyFiniteMarkAppendEquiv_preserving (n : ℕ) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyFiniteMarkAppendEquiv n (E := E))
      (π.prod (Measure.pi (fun _ : Fin n => π))) (Measure.pi (fun _ : Fin (n + 1) => π)) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => π) (Fin.last n)).symm _

/-- The real position bijection from old coordinates plus a fresh last coordinate to the canonical append. -/
def historyCanonicalAppendCoordinates (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Fin (historyShapeLength dependent g + 1) ≃ Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) :=
  (finCongr (by rw [historyShapeLength_out]; simp)).trans
    ((historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)).trans
      (finCongr (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm))

/-- Actual independent insertion followed by the actual canonical heap-coordinate permutation. -/
def historyCanonicalMarkAppendEquiv (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E] :
    E × (Fin (historyShapeLength dependent g) → E) ≃ᵐ
      (Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) → E) :=
  (historyFiniteMarkAppendEquiv (historyShapeLength dependent g)).trans
    (MeasurableEquiv.piCongrLeft (fun _ => E) (historyCanonicalAppendCoordinates dependent hsymm j g))

/-- The actual canonical append adds precisely one independent pi mark. -/
theorem historyCanonicalMarkAppendEquiv_preserving (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyCanonicalMarkAppendEquiv dependent hsymm j g (E := E))
      (π.prod (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)))
      (Measure.pi (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π)) :=
  (measurePreserving_piCongrLeft (fun _ => π) (historyCanonicalAppendCoordinates dependent hsymm j g)).comp
    (historyFiniteMarkAppendEquiv_preserving _ π)

/-- The actual maximal piece corresponding to the freshly appended update. -/
def historyCanonicalAppendedPiece (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    WordHeapPiece (historyShapeAppend dependent j g).out dependent :=
  historyCanonicalAppendHeapIso dependent hsymm j g (wordHeapAppendedPiece g.out dependent j)

omit [Fintype J] [LinearOrder J] in
theorem historyCanonicalAppendedPiece_maximal (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyCanonicalAppendedPiece dependent hsymm j g ∈ historyMaximalPieces Finset.univ := by
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  have hx : e (wordHeapAppendedPiece g.out dependent j) ∈ historyMaximalPieces
      ((Finset.univ : Finset (WordHeapPiece (g.out ++ [j]) dependent)).map e.toEquiv.toEmbedding) := by
    rw [historyMaximalPieces_orderIso_map]
    exact Finset.mem_map.2 ⟨_, wordHeapAppendedPiece_maximal g.out dependent j, rfl⟩
  rw [Finset.map_univ_equiv e.toEquiv] at hx
  exact hx

omit [Fintype J] [LinearOrder J] in
@[simp] theorem historyCanonicalAppendedPiece_label (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    wordHeapLabel (historyCanonicalAppendedPiece dependent hsymm j g) = j :=
  (historyCanonicalAppendHeapIso_label dependent hsymm j g _).trans
    (wordHeapAppendedPiece_label g.out dependent j)

/-- The freshly added coordinate in the canonical marked-history fiber. -/
def historyCanonicalFreshCoordinate (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) :=
  Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
    (historyCanonicalAppendedPiece dependent hsymm j g).position

theorem historyCanonicalAppendCoordinates_last (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyCanonicalAppendCoordinates dependent hsymm j g (Fin.last (historyShapeLength dependent g)) =
      historyCanonicalFreshCoordinate dependent hsymm j g := by
  let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
    rw [historyShapeLength_out]; simp
  have hl : (finCongr hlen) (Fin.last (historyShapeLength dependent g)) =
      (wordHeapAppendedPiece g.out dependent j).position := by
    apply Fin.ext
    exact historyShapeLength_out dependent g
  unfold historyCanonicalAppendCoordinates historyCanonicalFreshCoordinate historyCanonicalAppendedPiece
  change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
    (historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
      ((finCongr hlen) (Fin.last (historyShapeLength dependent g)))) = _
  rw [hl, historyHeapCoordinateEquiv_position]

@[simp] theorem historyFiniteMarkAppendEquiv_last (n : ℕ) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) :
    historyFiniteMarkAppendEquiv n (fresh, marks) (Fin.last n) = fresh := by
  have hh := congrArg Prod.fst
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).apply_symm_apply (fresh, marks))
  exact hh

/-- The canonical maximal-piece mark is exactly the independent fresh mark, including after reordering. -/
@[simp] theorem historyCanonicalMarkAppendEquiv_fresh (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength dependent g) → E) :
    historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)
      (historyCanonicalFreshCoordinate dependent hsymm j g) = fresh := by
  rw [← historyCanonicalAppendCoordinates_last]
  have hh := MeasurableEquiv.piCongrLeft_apply_apply
    (historyCanonicalAppendCoordinates dependent hsymm j g)
    (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks)) (Fin.last _)
  change MeasurableEquiv.piCongrLeft
    (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => E)
    (historyCanonicalAppendCoordinates dependent hsymm j g)
    (historyFiniteMarkAppendEquiv _ (fresh, marks))
    (historyCanonicalAppendCoordinates dependent hsymm j g (Fin.last (historyShapeLength dependent g))) = fresh
  rw [hh, historyFiniteMarkAppendEquiv_last]

end NearlyMinimax
