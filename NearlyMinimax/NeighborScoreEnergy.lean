module

public import NearlyMinimax.Risk


@[expose] public section

/-! Actual second-moment expansion of a finite score sum with bounded
dependency neighborhoods. Non-neighbor orthogonality is the structural input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem neighbor_pair_energy_sum_le {ι : Type*} [Fintype ι]
    (R : ι → ι → Prop) [DecidableRel R] (hsym : ∀ i j, R i j ↔ R j i) (D : ℕ)
    (hcard : ∀ i, (Finset.univ.filter (R i)).card ≤ D)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) :
    (∑ i, ∑ j, if R i j then (E i + E j) / 2 else 0) ≤ (D : ℝ) * ∑ i, E i := by
  classical
  have hf : (∑ i, ∑ j, if R i j then E i else 0) ≤ (D : ℝ) * ∑ i, E i := by
    calc
      _ = ∑ i, ((Finset.univ.filter (R i)).card : ℝ) * E i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i, (D : ℝ) * E i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i) (hE i)
      _ = _ := by rw [Finset.mul_sum]
  have hs : (∑ i, ∑ j, if R i j then E j else 0) =
      (∑ i, ∑ j, if R i j then E i else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [hsym j i]
  have hid : (∑ i, ∑ j, if R i j then (E i + E j) / 2 else 0) =
      ((∑ i, ∑ j, if R i j then E i else 0) +
        (∑ i, ∑ j, if R i j then E j else 0)) / 2 := by
    have hp (i j : ι) : (if R i j then (E i + E j) / 2 else 0) =
        ((if R i j then E i else 0) + (if R i j then E j else 0)) / 2 := by
      by_cases h : R i j <;> simp [h]
    calc
      _ = ∑ i, ∑ j, ((if R i j then E i else 0) + (if R i j then E j else 0)) / 2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))
      _ = _ := by
        simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hid, hs]
  linarith only [hf]

theorem secondMoment_sum_le_neighbor_degree
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (R : ι → ι → Prop) [DecidableRel R] (hsym : ∀ i j, R i j ↔ R j i) (D : ℕ)
    (hcard : ∀ i, (Finset.univ.filter (R i)).card ≤ D)
    (horth : ∀ i j, ¬ R i j → (∫ x, X i x * X j x ∂μ) = 0) :
    (∫ x, (∑ i, X i x) ^ 2 ∂μ) ≤ (D : ℝ) * ∑ i, ∫ x, X i x ^ 2 ∂μ := by
  classical
  let E (i : ι) := ∫ x, X i x ^ 2 ∂μ
  have hE (i : ι) : 0 ≤ E i := integral_nonneg (fun _ => sq_nonneg _)
  have hprod (i j : ι) : Integrable (fun x => X i x * X j x) μ :=
    (hX i).integrable_mul (hX j)
  have hpair (i j : ι) : (∫ x, X i x * X j x ∂μ) ≤
      if R i j then (E i + E j) / 2 else 0 := by
    by_cases hij : R i j
    · rw [if_pos hij]
      have h := integral_mono (hprod i j)
        (((hX i).integrable_sq.add (hX j).integrable_sq).div_const 2)
        (fun x => show X i x * X j x ≤ (X i x ^ 2 + X j x ^ 2) / 2 by
          nlinarith only [sq_nonneg (X i x - X j x)])
      rw [integral_div] at h
      change (∫ x, X i x * X j x ∂μ) ≤ (∫ x, X i x ^ 2 + X j x ^ 2 ∂μ) / 2 at h
      rw [integral_add (f := fun x => X i x ^ 2) (g := fun x => X j x ^ 2)
        (hX i).integrable_sq (hX j).integrable_sq] at h
      exact h
    · rw [if_neg hij, horth i j hij]
  have hexpand : (∫ x, (∑ i, X i x) ^ 2 ∂μ) =
      ∑ i, ∑ j, ∫ x, X i x * X j x ∂μ := by
    simp_rw [pow_two, Finset.sum_mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hprod i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hprod i j)
  rw [hexpand]
  exact (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))).trans
    (neighbor_pair_energy_sum_le R hsym D hcard E hE)

end NearlyMinimax
