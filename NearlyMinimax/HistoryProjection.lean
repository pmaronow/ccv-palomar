module

public import NearlyMinimax.HistoryShapes


@[expose] public section

/-!
# Dependent-pair projections determine a history shape

The projections of a word onto each dependent pair of labels are invariant
under consecutive independent exchanges. Conversely, equality of these
projections produces such exchanges, by moving the first letter through its
independent predecessors. This is the concrete injective encoding used for
the finite reference-law normalizer in `lower_heaps`.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [DecidableEq J]

def historyPairProjection (i j : J) (word : List J) : List J :=
  word.filter (fun x => decide (x = i ∨ x = j))

omit [DecidableEq J] in
theorem history_dependent_pair_members {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {i j x y : J} (hij : dependent i j) (hx : x = i ∨ x = j) (hy : y = i ∨ y = j) :
    dependent x y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hrefl _
  · exact hij
  · exact hsymm hij
  · exact hrefl _

theorem historyPairProjection_exchange {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {i j : J} (hij : dependent i j) {u v : List J}
    (h : IndependentHistoryExchange (fun a b => ¬ dependent a b) u v) :
    historyPairProjection i j u = historyPairProjection i j v := by
  cases h with
  | swap before after x y hxy =>
    by_cases hx : x = i ∨ x = j
    · have hy : ¬ (y = i ∨ y = j) := fun hy => hxy (history_dependent_pair_members hrefl hsymm hij hx hy)
      simp [historyPairProjection, List.filter_append, hx, hy]
    · by_cases hy : y = i ∨ y = j <;> simp [historyPairProjection, List.filter_append, hx, hy]

theorem historyPairProjection_shape_invariant {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {i j : J} (hij : dependent i j) {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    historyPairProjection i j u = historyPairProjection i j v := by
  induction h with
  | rel _ _ h => exact historyPairProjection_exchange hrefl hsymm hij h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem history_first_decomposition {a : J} {word : List J} (ha : a ∈ word) :
    ∃ before after, word = before ++ a :: after ∧ a ∉ before := by
  induction word with
  | nil => simp at ha
  | cons b word ih =>
    by_cases hba : b = a
    · subst b; exact ⟨[], word, rfl, by simp⟩
    · have ha' : a ∈ word := (List.mem_cons.1 ha).resolve_left (Ne.symm hba)
      obtain ⟨before, after, hword, hbefore⟩ := ih ha'
      exact ⟨b :: before, after, by simp [hword], by simp [hbefore, (Ne.symm hba)]⟩

theorem historyPairProjection_prefix_head {a b : J} {before after : List J}
    (ha : a ∉ before) (hb : b ∈ before) :
    (historyPairProjection a b (before ++ a :: after)).head? = some b := by
  induction before with
  | nil => simp at hb
  | cons c before ih =>
    have hca : c ≠ a := fun h => ha (List.mem_cons.2 (Or.inl h.symm))
    have habefore : a ∉ before := fun h => ha (List.mem_cons.2 (Or.inr h))
    by_cases hcb : c = b
    · subst c; simp [historyPairProjection]
    · have hbbefore : b ∈ before := (List.mem_cons.1 hb).resolve_left (Ne.symm hcb)
      simpa [historyPairProjection, hca, hcb] using ih habefore hbbefore

omit [DecidableEq J] in
theorem historyShapeRelation_cons {independent : J → J → Prop} (a : J) {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) :
    Relation.EqvGen (IndependentHistoryExchange independent) (a :: u) (a :: v) := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy =>
      exact .rel _ _ (IndependentHistoryExchange.swap (a :: before) after x y hxy)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

omit [DecidableEq J] in
theorem historyShapeRelation_move_first {independent : J → J → Prop} (a : J) (before after : List J)
    (hbefore : ∀ b ∈ before, independent b a) :
    Relation.EqvGen (IndependentHistoryExchange independent) (before ++ a :: after) (a :: (before ++ after)) := by
  induction before with
  | nil => exact .refl _
  | cons b before ih =>
    have hb := hbefore b (List.mem_cons_self)
    have hi := ih (fun c hc => hbefore c (List.mem_cons_of_mem _ hc))
    exact .trans _ _ _ (historyShapeRelation_cons b hi)
      (.rel _ _ (IndependentHistoryExchange.swap [] (before ++ after) b a hb))

/-- Equality of the actual dependent pair chains determines the history shape. -/
theorem historyShapeRelation_of_pair_projections {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {u v : List J} (hproj : ∀ i j, dependent i j → historyPairProjection i j u = historyPairProjection i j v) :
    Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact .refl _
    | cons b v =>
      have hh := congrArg List.head? (hproj b b (hrefl b))
      simp [historyPairProjection] at hh
  | cons a u ih =>
    have hamem : a ∈ v := by
      have hm : a ∈ historyPairProjection a a (a :: u) := by simp [historyPairProjection]
      rw [hproj a a (hrefl a)] at hm
      exact (List.mem_filter.1 hm).1
    obtain ⟨before, after, hv, ha⟩ := history_first_decomposition hamem
    have hind : ∀ b ∈ before, ¬ dependent b a := by
      intro b hb hba
      have hh := congrArg List.head? (hproj a b (hsymm hba))
      rw [hv, historyPairProjection_prefix_head ha hb] at hh
      have hab : a = b := by simpa [historyPairProjection] using hh
      exact ha (hab ▸ hb)
    have hmove := historyShapeRelation_move_first (independent := fun b c => ¬ dependent b c) a before after hind
    have hrest : ∀ i j, dependent i j → historyPairProjection i j u = historyPairProjection i j (before ++ after) := by
      intro i j hij
      have hm : historyPairProjection i j v = historyPairProjection i j (a :: (before ++ after)) := by
        rw [hv]
        exact historyPairProjection_shape_invariant hrefl hsymm hij hmove
      have hh := (hproj i j hij).trans hm
      by_cases hai : a = i ∨ a = j
      · simpa [historyPairProjection, hai] using hh
      · simpa [historyPairProjection, hai] using hh
    have hcons := historyShapeRelation_cons a (ih hrest)
    rw [hv]
    exact .trans _ _ _ hcons (.symm _ _ hmove)

def historyShapePairCode (dependent : J → J → Prop)
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) :
    HistoryShape (fun a b => ¬ dependent a b) → ({p : J × J // dependent p.1 p.2} → List J) :=
  Quotient.lift (fun word p => historyPairProjection p.val.1 p.val.2 word)
    (fun _ _ h => funext (fun p => historyPairProjection_shape_invariant hrefl hsymm p.prop h))

/-- The concrete pair-chain code is an injection on actual history shapes. -/
theorem historyShapePairCode_injective (dependent : J → J → Prop)
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) :
    Function.Injective (historyShapePairCode dependent hrefl hsymm) := by
  intro g h
  induction g using Quotient.inductionOn
  rename_i u
  induction h using Quotient.inductionOn
  rename_i v
  intro hcode
  apply Quotient.sound
  apply historyShapeRelation_of_pair_projections hrefl hsymm
  intro i j hij
  exact congrFun hcode ⟨⟨i, j⟩, hij⟩

end NearlyMinimax
