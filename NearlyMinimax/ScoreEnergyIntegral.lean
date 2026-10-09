module

public import NearlyMinimax.HighScoreTimeKernel


@[expose] public section

/-! The true square-root Fisher-energy integral is bounded by the path
length times the square root of its uniform energy budget. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax

theorem intervalIntegral_sqrt_energy_le (f : ℝ → ℝ) (T M : ℝ) (hT : 0 ≤ T)
    (hi : IntervalIntegrable (fun t => Real.sqrt (f t)) volume 0 T)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ M) :
    (∫ t in (0 : ℝ)..T, Real.sqrt (f t)) ≤ T * Real.sqrt M := by
  have h := intervalIntegral.integral_mono_on hT hi
    (intervalIntegrable_const (c := Real.sqrt M))
    (fun t ht => Real.sqrt_le_sqrt (hbound t ht))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

end NearlyMinimax
