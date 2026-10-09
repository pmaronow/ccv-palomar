module

public import NearlyMinimax.PoissonEnergyBounds


@[expose] public section

/-! Summation of the actual factorial-weighted score energy from finite
defect, alias, and field estimates and the full-response tail. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

def localScoreEnergy (x : ℝ) (r : ℕ → ℝ) : ℝ :=
  ∑' k, poissonCountWeight x k * r k

theorem poisson_energy_tail_bound {x C A : ℝ} (hx : 0 ≤ x)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (r : ℕ → ℝ) (hr0 : ∀ k, 0 ≤ r k) (a : ℕ)
    (hr : ∀ k, a ≤ k → r k ≤ A * C ^ k) :
    Summable (fun j => poissonCountWeight x (a + j) * r (a + j)) ∧
      (∑' j, poissonCountWeight x (a + j) * r (a + j)) ≤
        A * Real.exp (x * C) * poissonCountWeight (x * C) a := by
  have hm (j : ℕ) : poissonCountWeight x (a + j) * r (a + j) ≤
      A * poissonCountWeight (x * C) (a + j) := by
    calc
      _ ≤ poissonCountWeight x (a + j) * (A * C ^ (a + j)) :=
        mul_le_mul_of_nonneg_left (hr (a + j) (Nat.le_add_right _ _))
          (poissonCountWeight_nonneg hx _)
      _ = _ := by unfold poissonCountWeight; rw [mul_pow]; ring
  have hg : Summable (fun j => A * poissonCountWeight (x * C) (a + j)) :=
    ((poissonCountWeight_summable _).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)).mul_left A
  have hs : Summable (fun j => poissonCountWeight x (a + j) * r (a + j)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (poissonCountWeight_nonneg hx _) (hr0 _)) hm hg
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' j, A * poissonCountWeight (x * C) (a + j) := hs.tsum_le_tsum hm hg
    _ = A * ∑' j, poissonCountWeight (x * C) (a + j) := tsum_mul_left
    _ ≤ A * (Real.exp (x * C) * poissonCountWeight (x * C) a) :=
      mul_le_mul_of_nonneg_left (poissonCountWeight_tail_le (mul_nonneg hx hC) a) hA
    _ = _ := by ring

theorem local_energy_from_components {x C A Edef Eal Efld : ℝ}
    (hx : 0 ≤ x) (hC : 0 ≤ C) (hA : 0 ≤ A) (D : ℕ)
    (r rdef ral rfld : ℕ → ℝ) (hr0 : ∀ k, 0 ≤ r k)
    (hdecomp : ∀ k ≤ D, r k ≤ 3 * (rdef k + ral k + rfld k))
    (hdef : (∑ k ∈ Finset.range (D + 1), poissonCountWeight x k * rdef k) ≤ Edef)
    (hal : (∑ k ∈ Finset.range (D + 1), poissonCountWeight x k * ral k) ≤ Eal)
    (hfld : (∑ k ∈ Finset.range (D + 1), poissonCountWeight x k * rfld k) ≤ Efld)
    (hhi : ∀ k, D < k → r k ≤ A * C ^ k) :
    Summable (fun k => poissonCountWeight x k * r k) ∧
      localScoreEnergy x r ≤ 3 * (Edef + Eal + Efld) +
        A * Real.exp (x * C) * poissonCountWeight (x * C) (D + 1) := by
  have htail := poisson_energy_tail_bound hx hC hA r hr0 (D + 1)
    (fun k hk => hhi k (by omega))
  have hsum : Summable (fun k => poissonCountWeight x k * r k) := by
    apply (summable_nat_add_iff (D + 1)).mp
    simpa only [Nat.add_comm] using htail.1
  have hpre : (∑ k ∈ Finset.range (D + 1), poissonCountWeight x k * r k) ≤
      3 * (Edef + Eal + Efld) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (D + 1),
          poissonCountWeight x k * (3 * (rdef k + ral k + rfld k)) := by
        exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
          (hdecomp k (by have hk' := Finset.mem_range.mp hk; omega))
          (poissonCountWeight_nonneg hx k)
      _ = 3 * ((∑ k ∈ Finset.range (D + 1), poissonCountWeight x k * rdef k) +
          (∑ k ∈ Finset.range (D + 1), poissonCountWeight x k * ral k) +
          (∑ k ∈ Finset.range (D + 1), poissonCountWeight x k * rfld k)) := by
        simp_rw [show ∀ k, poissonCountWeight x k * (3 * (rdef k + ral k + rfld k)) =
          3 * (poissonCountWeight x k * rdef k + poissonCountWeight x k * ral k +
            poissonCountWeight x k * rfld k) from fun k => by ring]
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hdef hal) hfld) (by norm_num)
  refine ⟨hsum, ?_⟩
  unfold localScoreEnergy
  rw [← hsum.sum_add_tsum_nat_add (D + 1)]
  have ht : (∑' j, poissonCountWeight x (j + (D + 1)) * r (j + (D + 1))) ≤
      A * Real.exp (x * C) * poissonCountWeight (x * C) (D + 1) := by
    simpa only [Nat.add_comm] using htail.2
  exact add_le_add hpre ht

end NearlyMinimax
