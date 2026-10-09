module

public import NearlyMinimax.Model


@[expose] public section

/-! Exact passage from extended squared-risk lower bounds to root risk. -/
noncomputable section
namespace NearlyMinimax

theorem minimaxRMS_lower_of_squared_lower {d n : ℕ} (C : ModelConstants d)
    {r : ℝ} (hr : 0 ≤ r) (h : ENNReal.ofReal (r^2) ≤ minimaxRisk C n) :
    ENNReal.ofReal r ≤ minimaxRMS C n := by
  rw [ENNReal.ofReal_pow hr] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_natCast_mul] at hh
  norm_num only [Nat.cast_ofNat, mul_one_div_cancel, ENNReal.rpow_one] at hh
  exact hh

end NearlyMinimax
