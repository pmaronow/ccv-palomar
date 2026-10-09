module

public import NearlyMinimax.LowerSaddle


@[expose] public section

/-! The rounded deletion degree has a fixed linear bound in the source
resolution. The bound precedes the statistical sample and saddle shift. -/
noncomputable section
namespace NearlyMinimax

theorem lowerSaddleD_le_fixed_multiple {d m x : ℝ} (hd : 0 ≤ d)
    (hM : 1 ≤ (lowerSaddleM m x : ℝ)) :
    (lowerSaddleD d m x : ℝ) ≤ ((d+8)/4+1)*(lowerSaddleM m x : ℝ) := by
  have h := Nat.ceil_lt_add_one
    (mul_nonneg (by positivity : 0 ≤ (d+8)/4) (Nat.cast_nonneg (lowerSaddleM m x)))
  change (lowerSaddleD d m x : ℝ) < (d+8)/4*(lowerSaddleM m x : ℝ)+1 at h
  nlinarith only [h,hM]

end NearlyMinimax
