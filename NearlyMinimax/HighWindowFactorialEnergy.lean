module

public import NearlyMinimax.HighFrameDesignEnergy
public import NearlyMinimax.LocalEnergySeries


@[expose] public section

/-! Exact passage from the actual finite window/design count sum to the
local factorial series, retaining the geometric overlap and window factors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem highWindowLabels_card {d k : ℕ} [NeZero k] :
    Fintype.card (HighWindowLabels d k) = k ^ d := by
  simp only [HighWindowLabels, Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem high_window_factorial_energy_le {d k n : ℕ} [NeZero k]
    {x : ℝ} (hx : 0 ≤ x) (H : HighWindowLabels d k → ℕ → ℝ)
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r)
    (hH : ∀ j r, r ≤ n → H j r ≤ R r)
    (hs : Summable (fun r => poissonCountWeight x r * R r)) :
    (3 ^ d : ℕ) * ∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
      poissonCountWeight x r * H j r ≤
        (3 : ℝ) ^ d * (k : ℝ) ^ d * localScoreEnergy x R := by
  have hj (j : HighWindowLabels d k) :
      (∑ r ∈ Finset.range (n + 1), poissonCountWeight x r * H j r) ≤
        localScoreEnergy x R := by
    calc
      _ ≤ ∑ r ∈ Finset.range (n + 1), poissonCountWeight x r * R r := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hH j r (by
          have hh := Finset.mem_range.mp hr
          omega)) (poissonCountWeight_nonneg hx r)
      _ ≤ _ := hs.sum_le_tsum _ (fun r _ =>
        mul_nonneg (poissonCountWeight_nonneg hx r) (hR r))
  have hsum : (∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
      poissonCountWeight x r * H j r) ≤ ∑ _j : HighWindowLabels d k, localScoreEnergy x R :=
    Finset.sum_le_sum (fun j _ => hj j)
  have h := mul_le_mul_of_nonneg_left hsum
    (Nat.cast_nonneg (3 ^ d))
  simpa only [Finset.sum_const, Finset.card_univ, highWindowLabels_card,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using h

theorem high_design_factorial_parameter {d k n : ℕ} [NeZero k]
    (Csharp mu : ℝ) (hmu : mu = (n : ℝ) / (k : ℝ) ^ d) :
    (n : ℝ) * Csharp * (2 / (k : ℝ)) ^ d =
      (Csharp * (2 : ℝ) ^ d) * mu := by
  rw [hmu, div_pow]
  ring

theorem high_original_window_factorial_energy_le {d k n : ℕ} [NeZero k]
    (Csharp mu : ℝ) (hC : 0 ≤ Csharp) (hmu : mu = (n : ℝ) / (k : ℝ) ^ d)
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r)
    (hH : ∀ j r, r ≤ n →
      (∫ u, H j r u ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))) ≤ R r)
    (hs : Summable (fun r => poissonCountWeight ((Csharp * (2 : ℝ) ^ d) * mu) r * R r)) :
    (3 ^ d : ℕ) * ∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
      ((n : ℝ) * Csharp * (2 / (k : ℝ)) ^ d) ^ r / (r.factorial : ℝ) *
        ∫ u, H j r u ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) ≤
      (3 : ℝ) ^ d * (k : ℝ) ^ d * localScoreEnergy ((Csharp * (2 : ℝ) ^ d) * mu) R := by
  have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
  rw [high_design_factorial_parameter Csharp mu hmu]
  exact high_window_factorial_energy_le (mul_nonneg (mul_nonneg hC (by positivity)) hmu0)
    (fun j r => ∫ u, H j r u ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)))
    R hR hH hs

end NearlyMinimax
