module

public import NearlyMinimax.HistoryComponents
public import NearlyMinimax.WordHeap


@[expose] public section

/-!
# Upper-set connectivity in the actual cover graph

In a finite partially ordered history, an upward comparability edge is a
chain of covering edges. All its vertices remain inside an upper subset.
Thus the previously constructed components are exactly the cover-connected
components; this connects them to the actual heap degree bound in `WordHeap`.
-/

noncomputable section
namespace NearlyMinimax

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def historyCoverEdge (U : Finset α) (a b : α) : Prop :=
  a ∈ U ∧ b ∈ U ∧ (a ⋖ b ∨ b ⋖ a)

def HistoryCoverConnected (U : Finset α) (a b : α) : Prop :=
  Relation.EqvGen (historyCoverEdge U) a b

omit [DecidableEq α] in
theorem historyCoverConnected_comparable {U : Finset α} {a b : α}
    (h : HistoryCoverConnected U a b) : HistoryConnected U a b := by
  exact Relation.EqvGen.mono (r := historyCoverEdge U) (p := historyComparableEdge U)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)⟩) a b h

omit [DecidableEq α] in
theorem historyCoverConnected_of_le [Fintype α] {U : Finset α}
    (hU : IsHistoryUpper Finset.univ U) {a b : α} (ha : a ∈ U) (hab : a ≤ b) :
    HistoryCoverConnected U a b := by
  classical
  let : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  have hh := le_iff_reflTransGen_covBy.1 hab
  induction hh with
  | refl => exact .refl _
  | @tail c b hac hcb ih =>
    have hac' : a ≤ c := le_iff_reflTransGen_covBy.2 hac
    have hc : c ∈ U := hU.2 a ha c (Finset.mem_univ _) hac'
    have hb : b ∈ U := hU.2 a ha b (Finset.mem_univ _) (hac'.trans hcb.le)
    exact .trans _ _ _ (ih hac') (.rel _ _ ⟨hc, hb, Or.inl hcb⟩)

omit [DecidableEq α] in
/-- Actual upper-set comparability connectivity equals cover connectivity. -/
theorem historyConnected_iff_coverConnected [Fintype α] {U : Finset α}
    (hU : IsHistoryUpper Finset.univ U) {a b : α} :
    HistoryConnected U a b ↔ HistoryCoverConnected U a b := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
      rcases hab.2.2 with hab' | hba'
      · exact historyCoverConnected_of_le hU hab.1 hab'
      · exact .symm _ _ (historyCoverConnected_of_le hU hab.2.1 hba')
    | refl a => exact .refl _
    | symm a b hab ih => exact .symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact .trans _ _ _ ihab ihbc
  · exact historyCoverConnected_comparable

def historyInducedCoverGraph (U : Finset α) : SimpleGraph U where
  Adj a b := (a : α) ⋖ b ∨ (b : α) ⋖ a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.ne rfl) (fun h => h.ne rfl)⟩

def historyCoverGraph (α : Type*) [PartialOrder α] : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.ne rfl) (fun h => h.ne rfl)⟩

instance historyCoverGraph_locallyFinite [Fintype α] : (historyCoverGraph α).LocallyFinite :=
  fun _ => Fintype.ofFinite _

theorem historyCoverConnected_reachable {U : Finset α} {a b : α}
    (ha : a ∈ U) (hb : b ∈ U) (h : HistoryCoverConnected U a b) :
    (historyInducedCoverGraph U).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | rel a b hab => exact (show (historyInducedCoverGraph U).Adj ⟨a, hab.1⟩ ⟨b, hab.2.1⟩ from hab.2.2).reachable
  | refl a => exact SimpleGraph.Reachable.refl _
  | symm a b hab ih => exact (ih hb ha).symm
  | trans a b c hab hbc ihab ihbc =>
    by_cases hbU : b ∈ U
    · exact (ihab ha hbU).trans (ihbc hbU hb)
    · have hs : ∀ {x y}, HistoryCoverConnected U x y → x = y ∨ x ∈ U ∧ y ∈ U := by
        intro x y h
        induction h with
        | rel x y h => exact Or.inr ⟨h.1, h.2.1⟩
        | refl x => exact Or.inl rfl
        | symm x y h ih => exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        | trans x y z hxy hyz ihxy ihyz =>
          rcases ihxy with rfl | ⟨hx, hy⟩
          · exact ihyz
          · rcases ihyz with rfl | ⟨_, hz⟩
            · exact Or.inr ⟨hx, hy⟩
            · exact Or.inr ⟨hx, hz⟩
      rcases hs hab with hab' | hab'
      · exact (hbU (hab' ▸ ha)).elim
      · exact (hbU hab'.2).elim

omit [DecidableEq α] in
theorem historyInducedCoverGraph_reachable_connected {U : Finset α} {a b : U}
    (h : (historyInducedCoverGraph U).Reachable a b) :
    HistoryCoverConnected U a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons a c b hac p ih => exact .trans _ _ _ (.rel _ _ ⟨a.prop, c.prop, hac⟩) ih

theorem historyConnected_iff_coverGraph_reachable [Fintype α] {U : Finset α}
    (hU : IsHistoryUpper Finset.univ U) {a b : α} (ha : a ∈ U) (hb : b ∈ U) :
    HistoryConnected U a b ↔ (historyInducedCoverGraph U).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [historyConnected_iff_coverConnected hU]
  exact ⟨historyCoverConnected_reachable ha hb, historyInducedCoverGraph_reachable_connected⟩

theorem historyUpperPolymer_coverGraph_connected [Fintype α] {P : Finset α}
    (hP : P ∈ historyUpperPolymers Finset.univ) :
    ((historyCoverGraph α).induce (P : Set α)).Connected := by
  obtain ⟨hupper, hconn⟩ := mem_historyUpperPolymers.1 hP
  obtain ⟨x, hx⟩ := hconn.1
  let : Nonempty (P : Set α) := ⟨⟨x, hx⟩⟩
  constructor
  intro a b
  change (historyInducedCoverGraph P).Reachable a b
  exact (historyConnected_iff_coverGraph_reachable hupper a.prop b.prop).1 (hconn.2 a a.prop b b.prop)

end NearlyMinimax
