module

public import NearlyMinimax.ScoreCostAlgebra
public import Mathlib.Analysis.Normed.Algebra.Exponential


@[expose] public section

/-! Actual exponential-series tails used to sum the local score energies. -/
noncomputable section
namespace NearlyMinimax

def poissonCountWeight (x : ℝ) (k : ℕ) : ℝ := x ^ k / (k.factorial : ℝ)

theorem poissonCountWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ poissonCountWeight x k := by unfold poissonCountWeight; positivity

theorem poissonCountWeight_summable (x : ℝ) : Summable (poissonCountWeight x) :=
  Real.summable_pow_div_factorial x

theorem poissonCountWeight_tsum (x : ℝ) :
    (∑' k, poissonCountWeight x k) = Real.exp x := by
  simpa only [poissonCountWeight, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

theorem poissonCountWeight_add_le {x : ℝ} (hx : 0 ≤ x) (a j : ℕ) :
    poissonCountWeight x (a + j) ≤ poissonCountWeight x a * poissonCountWeight x j := by
  have hfNat : a.factorial * j.factorial ≤ (a + j).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a j)
  have hf : (a.factorial : ℝ) * (j.factorial : ℝ) ≤ ((a + j).factorial : ℝ) := by
    exact_mod_cast hfNat
  have h := div_le_div_of_nonneg_left (pow_nonneg hx (a + j))
    (mul_pos (by exact_mod_cast Nat.factorial_pos a) (by exact_mod_cast Nat.factorial_pos j)) hf
  simpa only [poissonCountWeight, pow_add, div_mul_div_comm] using h

theorem poissonCountWeight_tail_le {x : ℝ} (hx : 0 ≤ x) (a : ℕ) :
    (∑' j, poissonCountWeight x (a + j)) ≤ Real.exp x * poissonCountWeight x a := by
  have hs : Summable (fun j => poissonCountWeight x (a + j)) :=
    (poissonCountWeight_summable x).comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hg : Summable (fun j => poissonCountWeight x a * poissonCountWeight x j) :=
    (poissonCountWeight_summable x).mul_left _
  calc
    _ ≤ ∑' j, poissonCountWeight x a * poissonCountWeight x j :=
      hs.tsum_le_tsum (poissonCountWeight_add_le hx a) hg
    _ = Real.exp x * poissonCountWeight x a := by
      rw [tsum_mul_left, poissonCountWeight_tsum, mul_comm]

theorem poissonCountWeight_tail_le_of_bounded {x K : ℝ} (hx : 0 ≤ x)
    (hxK : x ≤ K) (a : ℕ) :
    (∑' j, poissonCountWeight x (a + j)) ≤ Real.exp K * poissonCountWeight x a :=
  (poissonCountWeight_tail_le hx a).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxK) (poissonCountWeight_nonneg hx a))

end NearlyMinimax
