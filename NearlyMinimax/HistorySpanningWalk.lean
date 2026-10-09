module

public import NearlyMinimax.HistoryCoverConnectivity


@[expose] public section

/-!
# Closed spanning walks of finite connected graphs

A finite connected graph has a closed walk based at any specified vertex,
visiting all vertices, of length twice the number of vertices minus two.
The proof constructs a spanning tree and deletes a leaf different from the
base vertex. This supplies the concrete encoding for the source's connected
upper-set count.
-/

noncomputable section
namespace NearlyMinimax

universe u

theorem finite_tree_closed_spanning_walk {V : Type u} [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) :
    ∃ p : T.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support := by
  classical
  have hmain : ∀ n : ℕ, ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (T : SimpleGraph V), T.IsTree → ∀ r : V,
        ∃ p : T.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support := by
    intro n
    induction n using Nat.strong_induction_on
    rename_i n ih
    intro V instV hcard T hT r
    by_cases hs : Subsingleton V
    · let : Subsingleton V := hs
      let : Unique V := { default := r, uniq := fun v => Subsingleton.elim v r }
      refine ⟨.nil, by simp, ?_⟩
      intro v
      simp [Subsingleton.elim v r]
    · let : Nontrivial V := not_subsingleton_iff_nontrivial.1 hs
      obtain ⟨a, b, hab, ha, hb⟩ := hT.exists_ne_and_degree_eq_one
      have hleaf : ∃ v : V, v ≠ r ∧ T.degree v = 1 := by
        by_cases har : a = r
        · exact ⟨b, fun hbr => hab (har.trans hbr.symm), hb⟩
        · exact ⟨a, har, ha⟩
      obtain ⟨v, hvr, hdeg⟩ := hleaf
      let S : Set V := {v}ᶜ
      let T' := T.induce S
      let r' : S := ⟨r, by simpa [S] using hvr.symm⟩
      have hT' : T'.IsTree := {
        connected := hT.connected.induce_compl_singleton_of_degree_eq_one hdeg
        isAcyclic := hT.isAcyclic.induce S }
      have hcard' : Fintype.card S = Fintype.card V - 1 := by
        simp only [S, Fintype.card_compl_set, Fintype.card_unique]
      have hlt : Fintype.card S < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := v) (by simp [S])
      obtain ⟨p', hp'len, hp'all⟩ := ih (Fintype.card S) hlt S rfl T' hT' r'
      let f : T' →g T := { toFun := Subtype.val, map_rel' := fun h => h }
      let p : T.Walk r r := p'.map f
      have hplen : p.length = 2 * (Fintype.card S - 1) := by
        simpa only [p, SimpleGraph.Walk.length_map] using hp'len
      have hpall : ∀ x : V, x ≠ v → x ∈ p.support := by
        intro x hxv
        rw [show p = p'.map f from rfl, SimpleGraph.Walk.support_map]
        exact List.mem_map.2 ⟨⟨x, by simpa [S] using hxv⟩, hp'all _, rfl⟩
      obtain ⟨w, hvw, _⟩ := T.degree_eq_one_iff_existsUnique_adj.1 hdeg
      have hwv : w ≠ v := hvw.ne.symm
      have hwp := hpall w hwv
      let left := p.takeUntil w hwp
      let right := p.dropUntil w hwp
      let excursion : T.Walk w w := .cons hvw.symm (.cons hvw .nil)
      let q := (left.append excursion).append right
      have hsplit : left.length + right.length = p.length := by
        have hh := congrArg SimpleGraph.Walk.length (p.take_spec hwp)
        simpa only [SimpleGraph.Walk.length_append] using hh
      have hqLen : q.length = 2 * (Fintype.card V - 1) := by
        simp only [q, excursion, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_nil]
        have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.2 inferInstance
        omega
      refine ⟨q, hqLen, ?_⟩
      intro x
      by_cases hxv : x = v
      · subst x
        simp only [q, SimpleGraph.Walk.mem_support_append_iff, excursion,
          SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons]
        exact Or.inl (Or.inr (Or.inr (Or.inl trivial)))
      · have hx := hpall x hxv
        have hxsplit : x ∈ left.support ∨ x ∈ right.support := by
          rw [← p.take_spec hwp, SimpleGraph.Walk.mem_support_append_iff] at hx
          exact hx
        simp only [q, SimpleGraph.Walk.mem_support_append_iff]
        exact hxsplit.elim (fun hx => Or.inl (Or.inl hx)) Or.inr
  exact hmain (Fintype.card V) V rfl T hT r

/-- The source's DFS encoding is available for every actual finite connected graph. -/
theorem finite_connected_closed_spanning_walk {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (r : V) :
    ∃ p : G.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  obtain ⟨p, hplen, hpall⟩ := finite_tree_closed_spanning_walk T hT r
  exact ⟨p.mapLe hTG, by simpa only [SimpleGraph.Walk.length_mapLe] using hplen,
    fun v => by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hpall v⟩

end NearlyMinimax
