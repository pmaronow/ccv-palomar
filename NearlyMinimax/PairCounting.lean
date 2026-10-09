module

public import Mathlib


@[expose] public section

noncomputable section
open scoped BigOperators Classical
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

theorem sum_orderedPairs {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ p ∈ orderedPairs n, f p) = ∑ i, ∑ j with j ≠ i, f (i, j) := by
  simp only [orderedPairs, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [ne_comm]

theorem orderedPairs_card (n : ℕ) : (orderedPairs n).card = n * (n - 1) := by
  have hfilter (i : Fin n) :
      Finset.univ.filter (fun j : Fin n => j ≠ i) = Finset.univ.erase i := by
    ext j
    simp
  have he := sum_orderedPairs (n := n) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at he
  simp only [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul] at he
  exact_mod_cast he

theorem orderedPairs_first_count {n : ℕ} (i : Fin n) :
    (∑ p ∈ orderedPairs n, if p.1 = i then (1 : ℝ) else 0) = (n - 1 : ℕ) := by
  rw [sum_orderedPairs, Finset.sum_eq_single i]
  · have hfilter :
        Finset.univ.filter (fun k : Fin n => k ≠ i) = Finset.univ.erase i := by
      ext k
      simp
    simp only [hfilter, ite_true]
    simp
  · intro j _ hji
    simp [hji]
  · simp

theorem sum_orderedPairs_swap {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ p ∈ orderedPairs n, f p.swap) = ∑ p ∈ orderedPairs n, f p := by
  apply Finset.sum_bij (fun p _ => p.swap)
  · intro p hp
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hp
  · intro a _ b _ hab
    exact Prod.swap_injective hab
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hb
  · intro p _
    rfl

theorem orderedPairs_second_count {n : ℕ} (i : Fin n) :
    (∑ p ∈ orderedPairs n, if p.2 = i then (1 : ℝ) else 0) = (n - 1 : ℕ) :=
  (sum_orderedPairs_swap (fun p : Fin n × Fin n => if p.1 = i then (1 : ℝ) else 0)).trans
    (orderedPairs_first_count i)

theorem orderedPairs_single_count {n : ℕ} {p : Fin n × Fin n}
    (hp : p ∈ orderedPairs n) :
    (∑ q ∈ orderedPairs n, if q = p then (1 : ℝ) else 0) = 1 := by
  simp [hp]

def overlapMajorant {n : ℕ} (p q : Fin n × Fin n) (A B : ℝ) : ℝ :=
  B * ((if q.1 = p.1 then 1 else 0) + (if q.2 = p.1 then 1 else 0) +
    (if q.1 = p.2 then 1 else 0) + (if q.2 = p.2 then 1 else 0)) +
  A * ((if q = p then 1 else 0) + (if q = p.swap then 1 else 0))

/-- Summing the four possible shared slots and two equal unordered pairs. -/
theorem overlap_majorant_sum {n : ℕ} {p : Fin n × Fin n}
    (hp : p ∈ orderedPairs n) (A B : ℝ) :
    (∑ q ∈ orderedPairs n, overlapMajorant p q A B) =
      4 * (n - 1 : ℕ) * B + 2 * A := by
  have hps : p.swap ∈ orderedPairs n := by
    simpa only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.swap, ne_comm] using hp
  simp only [overlapMajorant, Finset.sum_add_distrib, ← Finset.mul_sum,
    orderedPairs_first_count, orderedPairs_second_count,
    orderedPairs_single_count hp, orderedPairs_single_count hps]
  ring

end NearlyMinimax.PairUStatistic
