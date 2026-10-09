module

public import NearlyMinimax.HistoryDensityEmbedding
public import NearlyMinimax.HistoryMarkedAppend


@[expose] public section

/-!
# Actual prefix heap and deletion of the appended maximal piece
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*}

/-- Actual old positions embedded in the word with one appended occurrence. -/
def historyPrefixPosition (word : List J) (j : J) : Fin word.length ↪ Fin (word ++ [j]).length where
  toFun x := ⟨x.val, by have := x.isLt; simp only [List.length_append, List.length_singleton]; omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    exact congrArg (fun z : Fin (word ++ [j]).length => z.val) h

@[simp] theorem historyPrefixPosition_val (word : List J) (j : J) (x : Fin word.length) :
    (historyPrefixPosition word j x).val = x.val := rfl

/-- All existing labels retain their actual evaluation. -/
theorem historyPrefixPosition_get (word : List J) (j : J) (x : Fin word.length) :
    (word ++ [j]).get (historyPrefixPosition word j x) = word.get x := by
  change (word ++ [j]).get ⟨x.val, _⟩ = word.get x
  rw [List.get_eq_getElem, List.getElem_append_left x.isLt, List.get_eq_getElem]

/-- An appended word position lying inside the old word has the same label. -/
theorem historyPrefixPosition_get_of_lt (word : List J) (j : J)
    (x : Fin (word ++ [j]).length) (hx : x.val < word.length) :
    (word ++ [j]).get x = word.get ⟨x.val, hx⟩ := by
  rw [List.get_eq_getElem, List.getElem_append_left hx, List.get_eq_getElem]

/-- Existing generating edges embed into the genuinely appended dependency word. -/
theorem historyPrefixPosition_step (word : List J) (dependent : J → J → Prop) (j : J)
    {x y : Fin word.length} (hxy : historyPositionStep dependent word.get x y) :
    historyPositionStep dependent (word ++ [j]).get
      (historyPrefixPosition word j x) (historyPrefixPosition word j y) := by
  refine ⟨hxy.1, ?_⟩
  simpa only [historyPrefixPosition_get] using hxy.2

/-- A path whose endpoint is in the prefix cannot have passed through the appended occurrence. -/
theorem historyPrefixPosition_reachable_reflect (word : List J) (dependent : J → J → Prop) (j : J)
    {p q : Fin (word ++ [j]).length} (hp : p.val < word.length) (hq : q.val < word.length)
    (h : Relation.ReflTransGen (historyPositionStep dependent (word ++ [j]).get) p q) :
    Relation.ReflTransGen (historyPositionStep dependent word.get) ⟨p.val, hp⟩ ⟨q.val, hq⟩ := by
  induction h with
  | refl => exact .refl
  | @tail r q hreach hstep ih =>
    have hlt : r.val < q.val := hstep.1
    have hr : r.val < word.length := hlt.trans hq
    have hi := ih hr
    apply hi.tail
    refine ⟨hstep.1, ?_⟩
    simpa only [historyPrefixPosition_get_of_lt word j r hr, historyPrefixPosition_get_of_lt word j q hq] using hstep.2

/-- Exact reflection of the full actual heap relation in prefix positions. -/
theorem historyPrefixPosition_reachable_iff (word : List J) (dependent : J → J → Prop) (j : J)
    (x y : Fin word.length) :
    Relation.ReflTransGen (historyPositionStep dependent word.get) x y ↔
      Relation.ReflTransGen (historyPositionStep dependent (word ++ [j]).get)
        (historyPrefixPosition word j x) (historyPrefixPosition word j y) := by
  constructor
  · exact Relation.ReflTransGen.lift (historyPrefixPosition word j)
      (fun a b h => historyPrefixPosition_step word dependent j h) x y
  · intro h
    have hh := historyPrefixPosition_reachable_reflect word dependent j x.isLt y.isLt h
    cases x
    cases y
    exact hh

/-- The actual prefix dependency heap is an order embedding in the appended heap. -/
def historyPrefixHeapEmbedding (word : List J) (dependent : J → J → Prop) (j : J) :
    WordHeapPiece word dependent ↪o WordHeapPiece (word ++ [j]) dependent where
  toFun x := ⟨historyPrefixPosition word j x.position⟩
  inj' := by intro x y h; apply WordHeapPiece.ext; exact (historyPrefixPosition word j).injective (congrArg WordHeapPiece.position h)
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    exact (historyPrefixPosition_reachable_iff word dependent j x.position y.position).symm

@[simp] theorem historyPrefixHeapEmbedding_label (word : List J) (dependent : J → J → Prop)
    (j : J) (x : WordHeapPiece word dependent) :
    wordHeapLabel (historyPrefixHeapEmbedding word dependent j x) = wordHeapLabel x :=
  historyPrefixPosition_get word j x.position

/-- Deleting the appended maximal occurrence leaves exactly the image of the actual prefix heap. -/
theorem historyPrefixHeapEmbedding_univ (word : List J) (dependent : J → J → Prop) (j : J) :
    (Finset.univ : Finset (WordHeapPiece word dependent)).map (historyPrefixHeapEmbedding word dependent j).toEmbedding =
      (Finset.univ : Finset (WordHeapPiece (word ++ [j]) dependent)).erase (wordHeapAppendedPiece word dependent j) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    apply Finset.mem_erase.2
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    have hv := congrArg (fun z : WordHeapPiece (word ++ [j]) dependent => z.position.val) he
    have hlt := x.position.isLt
    change x.position.val = word.length at hv
    omega
  · intro hy
    have hne := (Finset.mem_erase.1 hy).1
    have hbound : y.position.val < word.length := by
      have hlt := y.position.isLt
      simp only [List.length_append, List.length_singleton] at hlt
      have hval : y.position.val ≠ word.length := by
        intro hv
        apply hne
        apply WordHeapPiece.ext
        apply Fin.ext
        exact hv
      omega
    let x : WordHeapPiece word dependent := ⟨⟨y.position.val, hbound⟩⟩
    refine Finset.mem_map.2 ⟨x, Finset.mem_univ _, ?_⟩
    apply WordHeapPiece.ext
    apply Fin.ext
    rfl

/-- Exact density deletion formula for the actual appended occurrence. -/
theorem historyPrefixHeap_density_delete (word : List J) (dependent : J → J → Prop)
    (j : J) (weight : WordHeapPiece (word ++ [j]) dependent → ℝ) (ρ t : ℝ) :
    historyScaledUpperDensity weight ρ (Finset.univ.erase (wordHeapAppendedPiece word dependent j)) t =
      historyScaledUpperDensity (weight ∘ historyPrefixHeapEmbedding word dependent j) ρ Finset.univ t := by
  rw [← historyPrefixHeapEmbedding_univ]
  exact historyScaledUpperDensity_orderEmbedding_map _ _ ρ _ t

end NearlyMinimax
