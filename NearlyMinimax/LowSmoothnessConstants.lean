module

public import NearlyMinimax.LowSmoothnessGridExperiment
public import NearlyMinimax.LowSmoothnessGridChoice


@[expose] public section

/-! Fixed prior constants constructed from the strict original-model margins. -/

noncomputable section
open Set
namespace NearlyMinimax

def lowSmoothnessScoreConstant {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) : ℝ :=
  (40 : ℝ) ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
    Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c)

theorem lowSmoothnessScoreConstant_nonneg {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) : 0 ≤ lowSmoothnessScoreConstant P := by
  unfold lowSmoothnessScoreConstant
  positivity

structure LowSmoothnessPriorConstants {d : ℕ} (C : ModelConstants d) where
  ternary : LowSmoothnessTernaryConstants C
  b : ℝ
  b_pos : 0 < b
  b_le_one : b ≤ 1
  field_guard : ((2 : ℝ) ^ d + 2) * b ≤ ternary.ρ
  variance_guard : b ^ 2 ≤ ternary.ρ
  holder_guard : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound
  score_guard : lowSmoothnessScoreConstant ternary * b ^ 4 ≤ 1

/-- All prior legality and score guards hold for a fixed positive amplitude. -/
theorem lowSmoothnessPriorConstants_exists {d : ℕ} (C : ModelConstants d) :
    Nonempty (LowSmoothnessPriorConstants C) := by
  obtain ⟨P⟩ := lowSmoothnessTernaryConstants_exists C
  let M := (2 : ℝ) ^ d + 2
  let H := (2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)
  let Q := lowSmoothnessScoreConstant P
  have hM : 0 < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hQ : 0 ≤ Q := lowSmoothnessScoreConstant_nonneg P
  let b := min (min (min (min 1 (P.ρ / M)) (Real.sqrt P.ρ)) (C.holderBound / H)) (1 / (Q + 1))
  have hb : 0 < b := lt_min
    (lt_min (lt_min (lt_min (by norm_num) (div_pos P.ρ_pos hM)) (Real.sqrt_pos.mpr P.ρ_pos))
      (div_pos C.holderBound_pos hH)) (div_pos (by norm_num) (by linarith))
  have hbQ : b ≤ 1 / (Q + 1) := min_le_right _ _
  have hbH : b ≤ C.holderBound / H := (min_le_left _ _).trans (min_le_right _ _)
  have hbS : b ≤ Real.sqrt P.ρ := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hbM : b ≤ P.ρ / M := (((min_le_left _ _).trans (min_le_left _ _)).trans
    (min_le_left _ _)).trans (min_le_right _ _)
  have hb1 : b ≤ 1 := (((min_le_left _ _).trans (min_le_left _ _)).trans
    (min_le_left _ _)).trans (min_le_left _ _)
  have hfield : M * b ≤ P.ρ := by
    have h := (le_div_iff₀ hM).mp hbM
    nlinarith
  have hvariance : b ^ 2 ≤ P.ρ := by
    nlinarith [Real.sq_sqrt P.ρ_pos.le, Real.sqrt_nonneg P.ρ]
  have hholder : H * b ≤ C.holderBound := by
    have h := (le_div_iff₀ hH).mp hbH
    nlinarith
  have hb4 : b ^ 4 ≤ b := by
    calc
      _ = b ^ 3 * b := by ring
      _ ≤ 1 * b := mul_le_mul_of_nonneg_right (pow_le_one₀ (n := 3) hb.le hb1) hb.le
      _ = b := one_mul b
  have hscore : Q * b ^ 4 ≤ 1 := by
    have h := (le_div_iff₀ (by linarith : 0 < Q + 1)).mp hbQ
    exact (mul_le_mul_of_nonneg_left hb4 hQ).trans (by nlinarith)
  exact ⟨⟨P, b, hb, hb1, hfield, hvariance, hholder, hscore⟩⟩

end NearlyMinimax
