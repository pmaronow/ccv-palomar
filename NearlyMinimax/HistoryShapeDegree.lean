module

public import NearlyMinimax.HistoryShapeCount
public import NearlyMinimax.WordHeap


@[expose] public section

/-!
# The actual dependent-degree shape-count exponent

Each distinct dependent pair contributes one binary interleaving. Counting
pair incidences label by label proves the exact exponent
`(Delta-1) * sum_j n_j` in the source reference-law estimate.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

def historyIncidentPairs (dependent : J → J → Prop) (j : J) : Finset (HistoryOrderedDependentPair dependent) := by
  classical
  exact Finset.univ.filter (fun p => p.val.1 = j ∨ p.val.2 = j)

def historyPairOtherLabel (dependent : J → J → Prop) (j : J)
    (p : HistoryOrderedDependentPair dependent) : J := if p.val.1 = j then p.val.2 else p.val.1

theorem historyIncidentPair_reconstruct (dependent : J → J → Prop) (j : J)
    (p : HistoryOrderedDependentPair dependent) (hp : p ∈ historyIncidentPairs dependent j) :
    p.val = if j < historyPairOtherLabel dependent j p then
      (j, historyPairOtherLabel dependent j p) else (historyPairOtherLabel dependent j p, j) := by
  rcases p with ⟨⟨a, b⟩, hab, hdep⟩
  obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
  dsimp at hp ⊢
  rcases hp with rfl | rfl
  · simp [historyPairOtherLabel, hab]
  · simp [historyPairOtherLabel, hab.ne, not_lt_of_gt hab]

theorem historyIncidentPairs_card_le (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (j : J) :
    (historyIncidentPairs dependent j).card ≤ (dependentLabelFinset dependent j).card - 1 := by
  classical
  have hj : j ∈ dependentLabelFinset dependent j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hrefl _⟩
  rw [← Finset.card_erase_of_mem hj]
  apply Finset.card_le_card_of_injOn (historyPairOtherLabel dependent j)
  · intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
    rcases hp with hp | hp
    · have he : historyPairOtherLabel dependent j p = p.val.2 := by simp [historyPairOtherLabel, hp]
      rw [he]
      apply Finset.mem_erase.2
      refine ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      · rw [← hp]; exact p.prop.1.ne.symm
      · rw [← hp]; exact p.prop.2
    · have hne : p.val.1 ≠ j := by rw [← hp]; exact p.prop.1.ne
      have he : historyPairOtherLabel dependent j p = p.val.1 := by simp [historyPairOtherLabel, hne]
      rw [he]
      exact Finset.mem_erase.2 ⟨hne, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [← hp]; exact hsymm p.prop.2⟩⟩
  · intro p hp q hq hpq
    apply Subtype.ext
    rw [historyIncidentPair_reconstruct dependent j p hp,
      historyIncidentPair_reconstruct dependent j q hq, hpq]

theorem historyPairExponent_incidence (dependent : J → J → Prop) (n : J → ℕ) :
    (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) =
      ∑ j : J, (historyIncidentPairs dependent j).card * n j := by
  classical
  have hp : ∀ p : HistoryOrderedDependentPair dependent,
      n p.val.1 + n p.val.2 = ∑ j : J, if p.val.1 = j ∨ p.val.2 = j then n j else 0 := by
    intro p
    have ht : ∀ j : J, (if p.val.1 = j ∨ p.val.2 = j then n j else 0) =
        (if p.val.1 = j then n j else 0) + (if p.val.2 = j then n j else 0) := by
      intro j
      by_cases h1 : p.val.1 = j
      · have h2 : p.val.2 ≠ j := fun h => p.prop.1.ne (h1.trans h.symm)
        simp [h1, h2]
      · by_cases h2 : p.val.2 = j <;> simp [h1, h2]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp [eq_comm]
  calc
    _ = ∑ p : HistoryOrderedDependentPair dependent, ∑ j : J, if p.val.1 = j ∨ p.val.2 = j then n j else 0 :=
      Finset.sum_congr rfl (fun p _ => hp p)
    _ = ∑ j : J, ∑ p : HistoryOrderedDependentPair dependent, if p.val.1 = j ∨ p.val.2 = j then n j else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp [historyIncidentPairs]

theorem historyPairExponent_le (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ) (n : J → ℕ) :
    (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) ≤ (Δ - 1) * ∑ j : J, n j := by
  rw [historyPairExponent_incidence, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.mul_le_mul_right (n j) ((historyIncidentPairs_card_le dependent hrefl hsymm j).trans
    (Nat.sub_le_sub_right (hlabels j) 1))

/-- The exact finite-multiplicity shape bound in `lower_heaps`. -/
theorem historyMultiplicityShape_card_le_degree (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ) (n : J → ℕ) :
    Nat.card (HistoryMultiplicityShape dependent n) ≤ 2 ^ ((Δ - 1) * ∑ j : J, n j) := by
  calc
    _ ≤ ∏ p : HistoryOrderedDependentPair dependent, 2 ^ (n p.val.1 + n p.val.2) :=
      historyMultiplicityShape_card_le dependent hrefl hsymm n
    _ = 2 ^ (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      (historyPairExponent_le dependent hrefl hsymm Δ hlabels n)

end NearlyMinimax
