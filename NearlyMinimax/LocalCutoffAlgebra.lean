module

public import NearlyMinimax.DefectTailSummation


@[expose] public section

/-! Exact numerical cancellation for the source's target-dependent spatial
cutoffs, and absorption of the genuine Taylor energy into interpolation scale. -/
noncomputable section
namespace NearlyMinimax

theorem target_cutoff_inverse_budget {d : ℕ} (hd : d ≠ 0)
    {N mu H : ℝ} (hN : 0 < N) (hmu : 0 < mu) (hH : 0 < H) (j : ℕ) :
    (N * (mu * H) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) * H ^ j =
      N ^ (-(d : ℝ)) / mu ^ j := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hprod : 0 < mu * H := mul_pos hmu hH
  rw [Real.mul_rpow hN.le (Real.rpow_pos_of_pos hprod _).le, ← Real.rpow_mul hprod.le]
  have he : ((j : ℝ) / d) * (-(d : ℝ)) = -(j : ℝ) := by field_simp
  rw [he, Real.rpow_neg hprod.le, Real.rpow_natCast, mul_pow]
  field_simp

theorem response_taylor_budget_absorption {eta N : ℝ} (hN : 0 < N)
    (q d : ℕ) (hsmall : eta ^ (4 * q) * N ^ d ≤ 1) :
    eta ^ (4 * q + 4) ≤ eta ^ 4 / N ^ d := by
  apply (le_div_iff₀ (pow_pos hN d)).mpr
  have h := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ eta ^ 4)
  simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm, mul_one] using h

end NearlyMinimax
