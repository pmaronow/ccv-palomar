module

public import NearlyMinimax.PilotSectionMoments


@[expose] public section

/-! The full coefficient pilot uses only the centered pilot second moment. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

theorem norm_add_sq_le_twice {H : Type*} [NormedAddCommGroup H] (u v : H) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (u + v)) (norm_add_le u v) 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem pilot_coefficient_memLp_two {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (u : H) {η : Ω → H} (hη : MemLp η 2 μ) :
    MemLp (fun x => u + η x) 2 μ := (memLp_const u).add hη

theorem pilot_coefficient_second_moment_le {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (u : H) {η : Ω → H} (hη : MemLp η 2 μ) {C R : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hE : (∫ x, ‖η x‖ ^ 2 ∂μ) ≤ R) :
    (∫ x, ‖u + η x‖ ^ 2 ∂μ) ≤ 2 * C ^ 2 + 2 * R := by
  have hT := (pilot_coefficient_memLp_two u hη).norm.integrable_sq
  have hηi := hη.norm.integrable_sq
  calc
    _ ≤ ∫ x, 2 * ‖u‖ ^ 2 + 2 * ‖η x‖ ^ 2 ∂μ := by
      exact integral_mono hT ((integrable_const _).add (hηi.const_mul 2))
        (fun x => norm_add_sq_le_twice u (η x))
    _ = 2 * ‖u‖ ^ 2 + 2 * ∫ x, ‖η x‖ ^ 2 ∂μ := by
      rw [integral_add (integrable_const _) (hηi.const_mul 2)]
      rw [integral_const, integral_const_mul]
      simp
    _ ≤ _ := by
      have hs := pow_le_pow_left₀ (norm_nonneg u) hu 2
      linarith

end NearlyMinimax.PilotFields
