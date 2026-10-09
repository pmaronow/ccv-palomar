module

public import NearlyMinimax.LocalCutoffAlgebra


@[expose] public section

/-! Genuine cutoff comparisons for selected and omitted target rows. -/
noncomputable section
namespace NearlyMinimax

theorem target_cutoff_le_base {d : ℕ} (hd : 0 < d)
    {N mu H : ℝ} (hN : 0 ≤ N) (hmuH : 0 ≤ mu * H) (hsmall : mu * H ≤ 1) (j : ℕ) :
    N * (mu * H) ^ ((j : ℝ) / d) ≤ N := by
  have h := Real.rpow_le_one hmuH hsmall (by positivity : 0 ≤ (j : ℝ) / d)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h hN

theorem target_cutoff_defect_budget_le {d : ℕ} (hd : d ≠ 0)
    {N mu : ℝ} (hN : 0 < N) (hmu : 0 < mu) (j : ℕ)
    (hT : 1 ≤ N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))
    (hTN : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) ≤ N) :
    (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) *
      (1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))) ^ j ≤
        N ^ (-(d : ℝ)) / mu ^ j := by
  have hN1 : 1 ≤ N := hT.trans hTN
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hlog : 1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ≤ 1 + Real.log N := by
    have ht : 0 < N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) := by linarith only [hT]
    have hh := Real.log_le_log ht hTN
    linarith only [hh]
  have hlog0 : 0 ≤ 1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) :=
    add_nonneg (by norm_num) (Real.log_nonneg hT)
  have hp : 0 ≤ (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog j) hp
  exact h.trans_eq (target_cutoff_inverse_budget hd hN hmu hH j)

theorem omitted_target_inverse_budget_ge_one {d : ℕ} (hd : d ≠ 0)
    {N mu : ℝ} (hN1 : 1 ≤ N) (hmu : 0 < mu) (j : ℕ)
    (hT : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) < 1) :
    1 ≤ N ^ (-(d : ℝ)) / mu ^ j := by
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hTp : 0 < N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) := by positivity
  rw [← target_cutoff_inverse_budget hd hN hmu hH j]
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hTp hT.le
    (by exact neg_nonpos.mpr (Nat.cast_nonneg d))
  have hH1 : 1 ≤ (1 + Real.log N) ^ j :=
    one_le_pow₀ (by linarith [Real.log_nonneg hN1])
  have h := mul_le_mul hp hH1 (by norm_num : (0 : ℝ) ≤ 1) (Real.rpow_nonneg hTp.le _)
  simpa only [one_mul] using h

end NearlyMinimax
