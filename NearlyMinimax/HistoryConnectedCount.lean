module

public import NearlyMinimax.HistorySpanningWalk


@[expose] public section

/-!
# The actual bounded-degree connected-subset count

A connected k-vertex subset containing a specified root is the support of a
closed walk of length 2(k-1). Distinct subsets give distinct support walks.
The walk count follows directly from the finite neighbor recursion. Thus the
source's connected-set bound is proved, rather than assumed as an activity
premise.
-/

noncomputable section
namespace NearlyMinimax

theorem graph_walk_count_le {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v).card ≤ D ^ n := by
  induction n generalizing u with
  | zero =>
    simp only [SimpleGraph.finsetWalkLength]
    split_ifs with h
    · subst u; simp
    · simp
  | succ n ih =>
    rw [SimpleGraph.finsetWalkLength]
    calc
      _ ≤ ∑ w : G.neighborSet u,
          ((G.finsetWalkLength n w v).map ⟨fun p => SimpleGraph.Walk.cons w.prop p, fun a b hab => by cases hab; rfl⟩).card :=
        Finset.card_biUnion_le
      _ = ∑ w : G.neighborSet u, (G.finsetWalkLength n w v).card := by simp
      _ ≤ ∑ _w : G.neighborSet u, D ^ n := Finset.sum_le_sum (fun _ _ => ih _)
      _ = G.degree u * D ^ n := by simp
      _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hD u)
      _ = D ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

def graphConnectedSubsets {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter (fun P => x ∈ P ∧ P.card = k ∧ (G.induce (P : Set V)).Connected)

theorem mem_graphConnectedSubsets {V : Type*} [Fintype V] {G : SimpleGraph V} {x : V} {k : ℕ} {P : Finset V} :
    P ∈ graphConnectedSubsets G x k ↔ x ∈ P ∧ P.card = k ∧ (G.induce (P : Set V)).Connected := by
  classical
  simp [graphConnectedSubsets]

theorem graphConnectedSubset_closed_walk {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x : V} {k : ℕ}
    {P : Finset V} (hP : P ∈ graphConnectedSubsets G x k) :
    ∃ p : G.Walk x x, p.length = 2 * (k - 1) ∧ p.support.toFinset = P := by
  classical
  obtain ⟨hx, hcard, hconn⟩ := mem_graphConnectedSubsets.1 hP
  let x' : P := ⟨x, hx⟩
  obtain ⟨p, hplen, hpall⟩ := finite_connected_closed_spanning_walk (G.induce (P : Set V)) hconn x'
  let f : G.induce (P : Set V) →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  refine ⟨p.map f, ?_, ?_⟩
  · have hc : Fintype.card (P : Set V) = P.card :=
      Fintype.card_ofFinset P (fun _ => Iff.rfl)
    simpa only [SimpleGraph.Walk.length_map, hc, hcard] using hplen
  · ext y
    rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact hzy ▸ z.prop
    · intro hy
      exact ⟨⟨y, hy⟩, hpall _, rfl⟩

/-- The source connected-set bound, uniformly in the number of vertices. -/
theorem graph_connected_subsets_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (x : V) (k : ℕ) :
    (graphConnectedSubsets G x k).card ≤ D ^ (2 * (k - 1)) := by
  classical
  let f : Finset V → G.Walk x x := fun P =>
    if hP : P ∈ graphConnectedSubsets G x k then Classical.choose (graphConnectedSubset_closed_walk hP) else .nil
  have hf : ∀ P ∈ graphConnectedSubsets G x k,
      (f P).length = 2 * (k - 1) ∧ (f P).support.toFinset = P := by
    intro P hP
    dsimp only [f]
    rw [dite_eq_left hP]
    exact Classical.choose_spec (graphConnectedSubset_closed_walk hP)
  calc
    _ ≤ (G.finsetWalkLength (2 * (k - 1)) x x).card := by
      apply Finset.card_le_card_of_injOn f
      · intro P hP
        exact SimpleGraph.mem_finsetWalkLength_iff.2 (hf P hP).1
      · intro P hP Q hQ hPQ
        calc
          P = (f P).support.toFinset := (hf P hP).2.symm
          _ = (f Q).support.toFinset := by rw [hPQ]
          _ = Q := (hf Q hQ).2
    _ ≤ _ := graph_walk_count_le G D hD _ _ _

end NearlyMinimax
