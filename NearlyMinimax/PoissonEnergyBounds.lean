module

public import NearlyMinimax.FactorialSeriesTail
public import Mathlib.Data.Nat.Choose.Bounds


@[expose] public section

/-! Binomial count energies are bounded by the actual factorial-weighted
series. Geometric full-response bounds prove that the series is finite. -/
noncomputable section
namespace NearlyMinimax

theorem binomialCountWeight_le {h : ℝ} (hh : 0 ≤ h) (n k : ℕ) :
    (n.choose k : ℝ) * h ^ k ≤ poissonCountWeight ((n : ℝ) * h) k := by
  have hc : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) :=
    Nat.choose_le_pow_div k n
  have h := mul_le_mul_of_nonneg_right hc (pow_nonneg hh k)
  simpa only [poissonCountWeight, mul_pow, div_mul_eq_mul_div] using h

theorem finite_binomial_energy_le_poisson {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hs : Summable (fun k => poissonCountWeight ((n : ℝ) * h) k * r k)) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * h ^ k * r k) ≤
      ∑' k, poissonCountWeight ((n : ℝ) * h) k * r k := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), poissonCountWeight ((n : ℝ) * h) k * r k := by
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_right (binomialCountWeight_le hh n k) (hr k)
    _ ≤ _ := hs.sum_le_tsum _ (fun k _ =>
      mul_nonneg (poissonCountWeight_nonneg (mul_nonneg (Nat.cast_nonneg _) hh) k) (hr k))

theorem geometric_poisson_energy_summable {x C A : ℝ} (hx : 0 ≤ x)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (r : ℕ → ℝ) (hr0 : ∀ k, 0 ≤ r k)
    (hr : ∀ k, r k ≤ A * C ^ k) :
    Summable (fun k => poissonCountWeight x k * r k) := by
  have hs : Summable (fun k => A * poissonCountWeight (x * C) k) :=
    (poissonCountWeight_summable _).mul_left A
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (poissonCountWeight_nonneg hx k) (hr0 k)) ?_ hs
  intro k
  have hh := mul_le_mul_of_nonneg_left (hr k) (poissonCountWeight_nonneg hx k)
  convert hh using 1 <;> unfold poissonCountWeight <;> rw [mul_pow] <;> ring

theorem polynomial_count_factor_le (k r : ℕ) :
    (k : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ k := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h := pow_le_pow_left₀ (Nat.cast_nonneg k) hk r
  simpa only [← pow_mul, Nat.mul_comm] using h

end NearlyMinimax
