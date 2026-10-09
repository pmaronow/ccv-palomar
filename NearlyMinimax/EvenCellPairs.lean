module

public import Mathlib


@[expose] public section

/-! The finite occupancy argument behind the hyperplane field moment bound. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

theorem even_cell_has_partner {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset J) (p : J → I) (h : ∀ i, Even ((s.filter (fun j => p j = i)).card))
    (a : J) (ha : a ∈ s) : ∃ b ∈ s, b ≠ a ∧ p b = p a := by
  let f := s.filter (fun j => p j = p a)
  have haf : a ∈ f := by simp [f, ha]
  have hpos : 0 < f.card := Finset.card_pos.mpr ⟨a, haf⟩
  have he : Even f.card := h (p a)
  obtain ⟨k, hk⟩ := he
  have htwo : 2 ≤ f.card := by omega
  have hne : 0 < (f.erase a).card := by
    rw [Finset.card_erase_of_mem haf]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hne
  have hb' := Finset.mem_erase.mp hb
  exact ⟨b, (Finset.mem_filter.mp hb'.2).1, hb'.1,
    (Finset.mem_filter.mp hb'.2).2⟩

theorem even_cells_erase_pair {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset J) (p : J → I) (h : ∀ i, Even ((s.filter (fun j => p j = i)).card))
    (a b : J) (ha : a ∈ s) (hb : b ∈ s) (hab : b ≠ a) (hp : p b = p a) :
    ∀ i, Even (((s.erase a).erase b).filter (fun j => p j = i)).card := by
  intro i
  rw [Finset.filter_erase, Finset.filter_erase]
  by_cases hpa : p a = i
  · have hai : a ∈ s.filter (fun j => p j = i) := by simp [ha, hpa]
    have hbi : b ∈ s.filter (fun j => p j = i) := by simp [hb, hp, hpa]
    have hbe : b ∈ (s.filter (fun j => p j = i)).erase a := by simp [hab, hbi]
    rw [Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem hai]
    obtain ⟨k, hk⟩ := h i
    have htwo : 2 ≤ (s.filter (fun j => p j = i)).card := by
      have hsub : ({a, b} : Finset J) ⊆ s.filter (fun j => p j = i) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hh := Finset.card_le_card hsub
      simpa [Ne.symm hab] using hh
    exact ⟨k - 1, by omega⟩
  · have hai : a ∉ s.filter (fun j => p j = i) := by simp [hpa]
    have hbi : b ∉ s.filter (fun j => p j = i) := by simp [hp, hpa]
    simp only [Finset.erase_eq_of_notMem hai, Finset.erase_eq_of_notMem hbi]
    exact h i

theorem even_cells_two_disjoint_pairs {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset J) (p : J → I) (hs : 4 ≤ s.card)
    (h : ∀ i, Even ((s.filter (fun j => p j = i)).card)) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ e ∈ s,
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧
        p b = p a ∧ p e = p c := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨b, hb, hab, hpab⟩ := even_cell_has_partner s p h a ha
  let t := (s.erase a).erase b
  have hbe : b ∈ s.erase a := by simp [hab, hb]
  have ht : 2 ≤ t.card := by
    simp only [t, Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  have heven := even_cells_erase_pair s p h a b ha hb hab hpab
  obtain ⟨e, he, hec, hpec⟩ := even_cell_has_partner t p heven c hc
  have hct := Finset.mem_erase.mp hc
  have hct' := Finset.mem_erase.mp hct.2
  have het := Finset.mem_erase.mp he
  have het' := Finset.mem_erase.mp het.2
  exact ⟨a, ha, b, hb, c, hct'.2, e, het'.2, hab, hct'.1, hct.1,
    het'.1, het.1, hec, hpab, hpec⟩

end NearlyMinimax
