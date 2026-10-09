module

public import NearlyMinimax.HistoryAppend


@[expose] public section

/-!
# Actual order transport under an adjacent independent exchange

Finite word positions generate heap order by earlier dependent labels. Swapping
two adjacent independent positions preserves every generating relation and its
transitive closure. This supplies the order component of marked-coordinate
transport without assuming representative invariance of a density.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} {n : ℕ}

def historyPositionStep (dependent : J → J → Prop) (labels : Fin n → J)
    (x y : Fin n) : Prop := x < y ∧ dependent (labels x) (labels y)

theorem historyAdjacent_swap_lt (labels : Fin n → J) (dependent : J → J → Prop)
    (i j x y : Fin n) (hij : i.val + 1 = j.val)
    (hind : ¬ dependent (labels i) (labels j))
    (hxy : historyPositionStep dependent labels x y) :
    Equiv.swap i j x < Equiv.swap i j y := by
  have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hlt : x.val < y.val := hxy.1
  by_cases hxi : x = i
  · subst x
    by_cases hyj : y = j
    · subst y; exact (hind hxy.2).elim
    · have hyi : y ≠ i := by intro he; subst y; simp at hlt
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyi hyj]
      change j.val < y.val
      have := Fin.val_ne_iff.2 hyj
      omega
  · by_cases hxj : x = j
    · subst x
      have hyi : y ≠ i := by intro he; subst y; omega
      have hyj : y ≠ j := by intro he; subst y; simp at hlt
      simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyi hyj]
      change i.val < y.val
      omega
    · by_cases hyi : y = i
      · subst y
        simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxi hxj]
        change x.val < j.val
        omega
      · by_cases hyj : y = j
        · subst y
          simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hxi hxj]
          change x.val < i.val
          have := Fin.val_ne_iff.2 hxi
          omega
        · simpa only [Equiv.swap_apply_of_ne_of_ne hxi hxj,
            Equiv.swap_apply_of_ne_of_ne hyi hyj] using hxy.1

/-- Each actual generating edge survives the independent exchange. -/
theorem historyAdjacent_swap_step (labels : Fin n → J) (dependent : J → J → Prop)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j))
    {x y : Fin n} (hxy : historyPositionStep dependent labels x y) :
    historyPositionStep dependent (labels ∘ Equiv.swap i j) (Equiv.swap i j x) (Equiv.swap i j y) := by
  refine ⟨historyAdjacent_swap_lt labels dependent i j x y hij hind hxy, ?_⟩
  simpa only [Function.comp_def, Equiv.swap_apply_self] using hxy.2

/-- The actual heap reachability relation survives the independent exchange. -/
theorem historyAdjacent_swap_reachable (labels : Fin n → J) (dependent : J → J → Prop)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j))
    {x y : Fin n} (hxy : Relation.ReflTransGen (historyPositionStep dependent labels) x y) :
    Relation.ReflTransGen (historyPositionStep dependent (labels ∘ Equiv.swap i j))
      (Equiv.swap i j x) (Equiv.swap i j y) := by
  induction hxy with
  | refl => exact .refl
  | tail hreach hstep ih => exact ih.tail (historyAdjacent_swap_step labels dependent i j hij hind hstep)

/-- Both directions of the actual heap order are transported by the same swap. -/
theorem historyAdjacent_swap_reachable_iff (labels : Fin n → J) (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j))
    (x y : Fin n) :
    Relation.ReflTransGen (historyPositionStep dependent labels) x y ↔
      Relation.ReflTransGen (historyPositionStep dependent (labels ∘ Equiv.swap i j))
        (Equiv.swap i j x) (Equiv.swap i j y) := by
  constructor
  · exact historyAdjacent_swap_reachable labels dependent i j hij hind
  · intro h
    have hind' : ¬ dependent ((labels ∘ Equiv.swap i j) i) ((labels ∘ Equiv.swap i j) j) := by
      simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact fun hd => hind (hsymm hd)
    have hh := historyAdjacent_swap_reachable (labels ∘ Equiv.swap i j) dependent i j hij hind' h
    simpa only [Function.comp_def, Equiv.swap_apply_self] using hh

/-- The actual word heap relation is its dependency relation on positions. -/
theorem wordHeap_le_iff_position_reachable (word : List J) (dependent : J → J → Prop)
    (x y : WordHeapPiece word dependent) :
    x ≤ y ↔ Relation.ReflTransGen (historyPositionStep dependent word.get) x.position y.position := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail hreach hstep ih => exact ih.tail hstep
  · intro h
    have hlift : ∀ {p q : Fin word.length},
        Relation.ReflTransGen (historyPositionStep dependent word.get) p q →
          Relation.ReflTransGen wordHeapStep (⟨p⟩ : WordHeapPiece word dependent) ⟨q⟩ := by
      intro p q hpq
      induction hpq with
      | refl => exact .refl
      | tail hreach hstep ih => exact ih.tail hstep
    cases x
    cases y
    exact hlift h

theorem historyEquiv_reachable_iff {A B : Type*} (e : A ≃ B)
    (r : A → A → Prop) (s : B → B → Prop)
    (hstep : ∀ x y, r x y ↔ s (e x) (e y)) (x y : A) :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · exact Relation.ReflTransGen.lift e (fun a b h => (hstep a b).1 h) x y
  · intro h
    have hlift := Relation.ReflTransGen.lift e.symm
      (r := s) (p := r) (fun a b h => by
        apply (hstep (e.symm a) (e.symm b)).2
        simpa only [e.apply_symm_apply] using h) (e x) (e y) h
    change Relation.ReflTransGen r (e.symm (e x)) (e.symm (e y)) at hlift
    simpa only [e.symm_apply_apply] using hlift

/-- Actual dependency heaps are isomorphic when their generating positions are. -/
def wordHeapOrderIsoPosition (word word' : List J) (dependent : J → J → Prop)
    (e : Fin word.length ≃ Fin word'.length)
    (hstep : ∀ x y, historyPositionStep dependent word.get x y ↔
      historyPositionStep dependent word'.get (e x) (e y)) :
    WordHeapPiece word dependent ≃o WordHeapPiece word' dependent where
  toFun x := ⟨e x.position⟩
  invFun x := ⟨e.symm x.position⟩
  left_inv x := WordHeapPiece.ext (e.symm_apply_apply x.position)
  right_inv x := WordHeapPiece.ext (e.apply_symm_apply x.position)
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    exact (historyEquiv_reachable_iff e _ _ hstep x.position y.position).symm

/-- Tuple positions and their actual finite word positions are canonically identical. -/
def historyTuplePositionEquiv (labels : Fin n → J) : Fin (List.ofFn labels).length ≃ Fin n :=
  finCongr List.length_ofFn

theorem historyTuplePositionEquiv_get (labels : Fin n → J) (i : Fin (List.ofFn labels).length) :
    (List.ofFn labels).get i = labels (historyTuplePositionEquiv labels i) := by
  exact List.get_ofFn labels i

/-- The actual word-position permutation of an adjacent tuple exchange. -/
def historyTupleSwapPositions (labels : Fin n → J) (i j : Fin n) :
    Fin (List.ofFn labels).length ≃ Fin (List.ofFn (labels ∘ Equiv.swap i j)).length :=
  (historyTuplePositionEquiv labels).trans
    ((Equiv.swap i j).trans (historyTuplePositionEquiv (labels ∘ Equiv.swap i j)).symm)

/-- Swapping adjacent independent updates constructs an actual dependency-heap order isomorphism. -/
def historyTupleSwapHeapIso (labels : Fin n → J) (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j)) :
    WordHeapPiece (List.ofFn labels) dependent ≃o
      WordHeapPiece (List.ofFn (labels ∘ Equiv.swap i j)) dependent :=
  wordHeapOrderIsoPosition _ _ dependent (historyTupleSwapPositions labels i j) (by
    intro x y
    unfold historyPositionStep
    simp only [historyTuplePositionEquiv_get]
    have hx : (historyTuplePositionEquiv (labels ∘ Equiv.swap i j))
        (historyTupleSwapPositions labels i j x) = Equiv.swap i j (historyTuplePositionEquiv labels x) := by
      simp [historyTupleSwapPositions]
    have hy : (historyTuplePositionEquiv (labels ∘ Equiv.swap i j))
        (historyTupleSwapPositions labels i j y) = Equiv.swap i j (historyTuplePositionEquiv labels y) := by
      simp [historyTupleSwapPositions]
    rw [hx, hy]
    simp only [Function.comp_def, Equiv.swap_apply_self]
    constructor
    · intro h
      have hpos : historyPositionStep dependent labels (historyTuplePositionEquiv labels x)
          (historyTuplePositionEquiv labels y) := by
        refine ⟨?_, h.2⟩
        simpa [historyTuplePositionEquiv, finCongr] using h.1
      have he := historyAdjacent_swap_lt labels dependent i j _ _ hij hind hpos
      exact ⟨by simpa [historyTupleSwapPositions, historyTuplePositionEquiv, finCongr] using he, h.2⟩
    · intro h
      have hnew : historyPositionStep dependent (labels ∘ Equiv.swap i j)
          (Equiv.swap i j (historyTuplePositionEquiv labels x))
          (Equiv.swap i j (historyTuplePositionEquiv labels y)) := by
        refine ⟨?_, ?_⟩
        · simpa [historyTupleSwapPositions, historyTuplePositionEquiv, finCongr] using h.1
        · simpa only [Function.comp_def, Equiv.swap_apply_self] using h.2
      have hind' : ¬ dependent ((labels ∘ Equiv.swap i j) i) ((labels ∘ Equiv.swap i j) j) := by
        simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
        exact fun hd => hind (hsymm hd)
      have he := historyAdjacent_swap_lt (labels ∘ Equiv.swap i j) dependent i j _ _ hij hind' hnew
      exact ⟨by simpa [historyTuplePositionEquiv, finCongr] using he, h.2⟩)

end NearlyMinimax
