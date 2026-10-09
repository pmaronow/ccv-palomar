module

public import NearlyMinimax.HistoryPolynomial
public import Mathlib


@[expose] public section

/-!
# The actual dependency partial order of a finite history word

Pieces are occurrences in the word. Earlier dependent occurrences generate
the heap order. Antisymmetry is proved using their positions. In particular,
dependent labels are comparable, maximal pieces have distinct labels, and
the cover graph has at most one upper and one lower cover of each dependent
label. These are the combinatorial facts used in `lower_heaps`.
-/

noncomputable section
namespace NearlyMinimax

structure WordHeapPiece {J : Type*} (word : List J) (dependent : J → J → Prop) where
  position : Fin word.length

@[ext] theorem WordHeapPiece.ext {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : x.position = y.position) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance wordHeapPiece_decidableEq {J : Type*} (word : List J) (dependent : J → J → Prop) :
    DecidableEq (WordHeapPiece word dependent) := Classical.decEq _

instance wordHeapPiece_fintype {J : Type*} (word : List J) (dependent : J → J → Prop) :
    Fintype (WordHeapPiece word dependent) :=
  Fintype.ofEquiv (Fin word.length) {
    toFun := fun i => ⟨i⟩
    invFun := WordHeapPiece.position
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def wordHeapLabel {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : J := word.get x.position

def wordHeapStep {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x y : WordHeapPiece word dependent) : Prop :=
  x.position < y.position ∧ dependent (wordHeapLabel x) (wordHeapLabel y)

theorem wordHeap_reachable_position_le {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : Relation.ReflTransGen wordHeapStep x y) :
    x.position ≤ y.position := by
  induction h with
  | refl => exact le_rfl
  | tail hreach hstep ih => exact ih.trans hstep.1.le

instance wordHeap_partialOrder {J : Type*} (word : List J) (dependent : J → J → Prop) :
    PartialOrder (WordHeapPiece word dependent) where
  le := Relation.ReflTransGen wordHeapStep
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm x y hxy hyx := by
    apply WordHeapPiece.ext
    exact le_antisymm (wordHeap_reachable_position_le hxy) (wordHeap_reachable_position_le hyx)

theorem wordHeapStep_le {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : wordHeapStep x y) : x ≤ y :=
  Relation.ReflTransGen.single h

theorem wordHeap_dependent_comparable {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) {x y : WordHeapPiece word dependent}
    (hdep : dependent (wordHeapLabel x) (wordHeapLabel y)) : x ≤ y ∨ y ≤ x := by
  rcases lt_trichotomy x.position y.position with hxy | heq | hyx
  · exact Or.inl (wordHeapStep_le ⟨hxy, hdep⟩)
  · have hxy : x = y := WordHeapPiece.ext heq
    subst y
    exact Or.inl le_rfl
  · exact Or.inr (wordHeapStep_le ⟨hyx, hsymm hdep⟩)

theorem wordHeap_cover_dependent {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (hcov : x ⋖ y) :
    dependent (wordHeapLabel x) (wordHeapLabel y) := by
  have hxy : Relation.ReflTransGen wordHeapStep x y := hcov.le
  cases hxy with
  | refl => exact (hcov.ne rfl).elim
  | @tail z y hxz hzy =>
    have hbetween := hcov.eq_or_eq hxz (wordHeapStep_le hzy)
    rcases hbetween with rfl | hzyEq
    · exact hzy.2
    · have hh : z.position < z.position := by simpa only [hzyEq] using hzy.1
      exact (lt_irrefl _ hh).elim

theorem wordHeap_equal_labels_comparable {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {x y : WordHeapPiece word dependent} (hlab : wordHeapLabel x = wordHeapLabel y) :
    x ≤ y ∨ y ≤ x := by
  apply wordHeap_dependent_comparable hsymm
  rw [hlab]
  exact hrefl _

theorem wordHeap_upper_cover_label_injective {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {x y z : WordHeapPiece word dependent} (hxy : x ⋖ y) (hxz : x ⋖ z)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases wordHeap_equal_labels_comparable hrefl hsymm hlab with hyz | hzy
  · rcases hxz.eq_or_eq hxy.le hyz with hyx | hyz
    · exact (hxy.ne hyx.symm).elim
    · exact hyz
  · rcases hxy.eq_or_eq hxz.le hzy with hzx | hzy
    · exact (hxz.ne hzx.symm).elim
    · exact hzy.symm

theorem wordHeap_lower_cover_label_injective {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {x y z : WordHeapPiece word dependent} (hyx : y ⋖ x) (hzx : z ⋖ x)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases wordHeap_equal_labels_comparable hrefl hsymm hlab with hyz | hzy
  · rcases hyx.eq_or_eq hyz hzx.le with hzy | hzxEq
    · exact hzy.symm
    · exact (hzx.ne hzxEq).elim
  · rcases hzx.eq_or_eq hzy hyx.le with hyz | hyxEq
    · exact hyz
    · exact (hyx.ne hyxEq).elim

theorem wordHeap_maximal_label_injective {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (S : Finset (WordHeapPiece word dependent)) :
    Set.InjOn wordHeapLabel (historyMaximalPieces S : Set (WordHeapPiece word dependent)) := by
  intro x hx y hy hlab
  obtain ⟨hxS, hxmax⟩ := mem_historyMaximalPieces.1 hx
  obtain ⟨hyS, hymax⟩ := mem_historyMaximalPieces.1 hy
  rcases wordHeap_equal_labels_comparable hrefl hsymm hlab with hxy | hyx
  · exact (hxmax y hyS hxy).symm
  · exact hymax x hxS hyx

theorem wordHeap_maximal_card_le_labels {J : Type*} [Fintype J] [DecidableEq J]
    {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (S : Finset (WordHeapPiece word dependent)) :
    (historyMaximalPieces S).card ≤ Fintype.card J := by
  rw [← Finset.card_image_iff.2 (wordHeap_maximal_label_injective hrefl hsymm S)]
  exact Finset.card_le_card (Finset.subset_univ _)

def wordHeapUpperCovers {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : Finset (WordHeapPiece word dependent) := by
  classical
  exact Finset.univ.filter (fun y => x ⋖ y)

def wordHeapLowerCovers {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : Finset (WordHeapPiece word dependent) := by
  classical
  exact Finset.univ.filter (fun y => y ⋖ x)

def dependentLabelFinset {J : Type*} [Fintype J] (dependent : J → J → Prop) (j : J) : Finset J := by
  classical
  exact Finset.univ.filter (fun i => dependent j i)

theorem wordHeap_upper_covers_card {J : Type*} [Fintype J] {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (x : WordHeapPiece word dependent) :
    (wordHeapUpperCovers x).card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  classical
  apply Finset.card_le_card_of_injOn wordHeapLabel
  · intro y hy
    have hxy : x ⋖ y := (Finset.mem_filter.1 hy).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, wordHeap_cover_dependent hxy⟩
  · intro y hy z hz hlab
    exact wordHeap_upper_cover_label_injective hrefl hsymm
      (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2 hlab

theorem wordHeap_lower_covers_card {J : Type*} [Fintype J] {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (x : WordHeapPiece word dependent) :
    (wordHeapLowerCovers x).card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  classical
  apply Finset.card_le_card_of_injOn wordHeapLabel
  · intro y hy
    have hyx : y ⋖ x := (Finset.mem_filter.1 hy).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsymm (wordHeap_cover_dependent hyx)⟩
  · intro y hy z hz hlab
    exact wordHeap_lower_cover_label_injective hrefl hsymm
      (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2 hlab

def wordHeapCoverGraph {J : Type*} (word : List J) (dependent : J → J → Prop) :
    SimpleGraph (WordHeapPiece word dependent) where
  Adj x y := x ⋖ y ∨ y ⋖ x
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by
    rcases h with h | h <;> exact h.ne rfl⟩

instance wordHeapCoverGraph_neighbor_fintype {J : Type*} (word : List J) (dependent : J → J → Prop)
    (x : WordHeapPiece word dependent) : Fintype ((wordHeapCoverGraph word dependent).neighborSet x) :=
  Fintype.ofFinite _

theorem wordHeapCoverGraph_neighbors {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) :
    (wordHeapCoverGraph word dependent).neighborFinset x = wordHeapUpperCovers x ∪ wordHeapLowerCovers x := by
  classical
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  simp only [wordHeapUpperCovers, wordHeapLowerCovers, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rfl

/-- The cover graph's degree is bounded by twice the number of dependent labels, uniformly in history size. -/
theorem wordHeapCoverGraph_degree_le {J : Type*} [Fintype J] {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (x : WordHeapPiece word dependent) :
    (wordHeapCoverGraph word dependent).degree x ≤
      2 * (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  classical
  change ((wordHeapCoverGraph word dependent).neighborFinset x).card ≤ _
  rw [wordHeapCoverGraph_neighbors]
  have hupper := wordHeap_upper_covers_card hrefl hsymm x
  have hlower := wordHeap_lower_covers_card hrefl hsymm x
  have hunion := Finset.card_union_le (wordHeapUpperCovers x) (wordHeapLowerCovers x)
  omega

end NearlyMinimax
