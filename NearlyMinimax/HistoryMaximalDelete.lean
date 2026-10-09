module

public import NearlyMinimax.HistoryWordTransport


@[expose] public section

/-!
# Actual maximal-piece deletion inverts quotient append
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*}

/-- Shape equivalence can be prefixed by any word. -/
theorem historyShapeRelation_prefix {independent : J → J → Prop} (preword : List J)
    {u v : List J} (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) :
    Relation.EqvGen (IndependentHistoryExchange independent) (preword ++ u) (preword ++ v) := by
  induction preword with
  | nil => exact h
  | cons a preword ih => exact historyShapeRelation_cons a ih

/-- A piece can be moved to the last position precisely across independent following labels. -/
theorem historyShapeRelation_move_last {independent : J → J → Prop} (a : J) (after : List J)
    (hafter : ∀ b ∈ after, independent a b) :
    Relation.EqvGen (IndependentHistoryExchange independent) (a :: after) (after ++ [a]) := by
  induction after with
  | nil => exact .refl _
  | cons b after ih =>
    have hb := hafter b List.mem_cons_self
    have hi := ih (fun c hc => hafter c (List.mem_cons_of_mem _ hc))
    exact .trans _ _ _ (.rel _ _ (IndependentHistoryExchange.swap [] after a b hb))
      (historyShapeRelation_cons b hi)

/-- The concrete word obtained by deleting one specified actual occurrence. -/
def historyWordDeletePiece (word : List J) (dependent : J → J → Prop)
    (x : WordHeapPiece word dependent) : List J :=
  word.take x.position.val ++ word.drop (x.position.val + 1)

/-- Every label after a maximal occurrence is independent of it. -/
theorem wordHeap_maximal_suffix_independent (word : List J) (dependent : J → J → Prop)
    (x : WordHeapPiece word dependent) (hx : x ∈ historyMaximalPieces Finset.univ) :
    ∀ b ∈ word.drop (x.position.val + 1), ¬ dependent (wordHeapLabel x) b := by
  intro b hb hdep
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.1 hb
  have hybound : x.position.val + 1 + k < word.length := by
    simp only [List.length_drop] at hk
    omega
  let y : WordHeapPiece word dependent := ⟨⟨x.position.val + 1 + k, hybound⟩⟩
  have hylabel : wordHeapLabel y = b := by
    change word.get ⟨x.position.val + 1 + k, hybound⟩ = b
    rw [List.get_eq_getElem]
    simpa only [List.getElem_drop] using hkb
  have hxy : x ≤ y := wordHeapStep_le ⟨by dsimp [y]; change x.position.val < x.position.val + 1 + k; omega,
    by simpa only [hylabel] using hdep⟩
  have he := (mem_historyMaximalPieces.1 hx).2 y (Finset.mem_univ y) hxy
  have hv : x.position.val + 1 + k = x.position.val := congrArg (fun z : WordHeapPiece word dependent => z.position.val) he
  omega

/-- The actual word heap deletion has exactly the shape required by append. -/
theorem wordHeap_maximal_delete_shape (word : List J) (dependent : J → J → Prop)
    (x : WordHeapPiece word dependent) (hx : x ∈ historyMaximalPieces Finset.univ) :
    Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b))
      word (historyWordDeletePiece word dependent x ++ [wordHeapLabel x]) := by
  have hmove := historyShapeRelation_move_last (independent := fun a b => ¬ dependent a b) (wordHeapLabel x)
    (word.drop (x.position.val + 1)) (wordHeap_maximal_suffix_independent word dependent x hx)
  have hprefix := historyShapeRelation_prefix (word.take x.position.val) hmove
  have hword : word = word.take x.position.val ++ wordHeapLabel x :: word.drop (x.position.val + 1) := by
    change word = word.take x.position.val ++ word.get x.position :: word.drop (x.position.val + 1)
    rw [List.cons_get_drop_succ]
    exact (List.take_append_drop _ _).symm
  conv_lhs => rw [hword]
  simpa only [historyWordDeletePiece, List.append_assoc] using hprefix

variable [Fintype J] [LinearOrder J]

omit [Fintype J] [LinearOrder J] in
/-- Deleting a true maximal piece is a genuine preimage of its labelled append map. -/
theorem wordHeap_maximal_delete_append (word : List J) (dependent : J → J → Prop)
    (x : WordHeapPiece word dependent) (hx : x ∈ historyMaximalPieces Finset.univ) :
    historyShapeAppend dependent (wordHeapLabel x) (Quotient.mk _ (historyWordDeletePiece word dependent x)) =
      (Quotient.mk _ word : HistoryShape (fun a b => ¬ dependent a b)) := by
  rw [historyShapeAppend_mk]
  exact (Quotient.sound (wordHeap_maximal_delete_shape word dependent x hx)).symm

/-- The concrete last occurrence in a word with an appended label. -/
def wordHeapAppendedPiece (word : List J) (dependent : J → J → Prop) (j : J) :
    WordHeapPiece (word ++ [j]) dependent := ⟨⟨word.length, by simp⟩⟩

omit [Fintype J] [LinearOrder J] in
@[simp] theorem wordHeapAppendedPiece_label (word : List J) (dependent : J → J → Prop) (j : J) :
    wordHeapLabel (wordHeapAppendedPiece word dependent j) = j := by
  unfold wordHeapLabel wordHeapAppendedPiece
  rw [List.get_eq_getElem, List.getElem_append_right (by rfl)]
  simp

omit [Fintype J] [LinearOrder J] in
theorem wordHeapAppendedPiece_maximal (word : List J) (dependent : J → J → Prop) (j : J) :
    wordHeapAppendedPiece word dependent j ∈ historyMaximalPieces Finset.univ := by
  apply mem_historyMaximalPieces.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro y hy hxy
  have hlo := wordHeap_reachable_position_le hxy
  have hhi := y.position.isLt
  simp only [List.length_append, List.length_singleton] at hhi
  apply WordHeapPiece.ext
  apply Fin.ext
  change word.length ≤ y.position.val at hlo
  change y.position.val = word.length
  omega

omit [Fintype J] [LinearOrder J] in
/-- The terminal-shape range is exactly the genuine maximal-piece label condition. -/
theorem historyShape_terminal_iff_maximal (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    g ∈ Set.range (historyShapeAppend dependent j) ↔
      ∃ x : WordHeapPiece g.out dependent,
        x ∈ historyMaximalPieces Finset.univ ∧ wordHeapLabel x = j := by
  constructor
  · rintro ⟨u, hu⟩
    have hmk : (Quotient.mk _ (u.out ++ [j]) : HistoryShape (fun a b => ¬ dependent a b)) = g := by
      calc
        _ = historyShapeAppend dependent j (Quotient.mk _ u.out) := rfl
        _ = historyShapeAppend dependent j u := congrArg _ (Quotient.out_eq u)
        _ = g := hu
    have hr : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b))
        (u.out ++ [j]) g.out := Quotient.exact (hmk.trans (Quotient.out_eq g).symm)
    obtain ⟨e, he⟩ := historyShapeRelation_heapIso dependent hsymm hr
    let x := wordHeapAppendedPiece u.out dependent j
    have hx := wordHeapAppendedPiece_maximal u.out dependent j
    have hxmap : e x ∈ historyMaximalPieces ((Finset.univ : Finset (WordHeapPiece (u.out ++ [j]) dependent)).map e.toEquiv.toEmbedding) := by
      rw [historyMaximalPieces_orderIso_map]
      exact Finset.mem_map.2 ⟨x, hx, rfl⟩
    rw [Finset.map_univ_equiv e.toEquiv] at hxmap
    exact ⟨e x, hxmap, (he x).trans (wordHeapAppendedPiece_label u.out dependent j)⟩
  · rintro ⟨x, hx, hlabel⟩
    have hd := wordHeap_maximal_delete_append g.out dependent x hx
    rw [hlabel] at hd
    exact ⟨Quotient.mk _ (historyWordDeletePiece g.out dependent x), hd.trans (Quotient.out_eq g)⟩

end NearlyMinimax
