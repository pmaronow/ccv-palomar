module

public import NearlyMinimax.ProjectionStatistical


@[expose] public section

open scoped ENNReal

noncomputable section
namespace NearlyMinimax

/-- Subdivisions per coordinate at half the sample's column budget. -/
def projectionGridSize (d n : ℕ) : ℕ :=
  ⌊((n : ℝ) / 2) ^ ((d : ℝ)⁻¹)⌋₊

/-- Flooring the half-sample root yields a nonempty grid with at most
half as many cells as observations. -/
theorem projection_grid_size_spec {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n) :
    0 < projectionGridSize d n ∧
    (projectionGridSize d n : ℝ) ^ d ≤ (n : ℝ) / 2 ∧
    ((n : ℝ) / 2) ^ ((d : ℝ)⁻¹) ≤ 2 * projectionGridSize d n := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let r := ((n : ℝ) / 2) ^ ((d : ℝ)⁻¹)
  have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith) (inv_nonneg.mpr hdreal.le)
  have hk : 0 < projectionGridSize d n := Nat.floor_pos.mpr hr1
  have hkle : (projectionGridSize d n : ℝ) ≤ r := Nat.floor_le (by positivity)
  have hbudget : (projectionGridSize d n : ℝ) ^ d ≤ (n : ℝ) / 2 := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hkle d).trans
    simpa only [r] using le_of_eq (Real.rpow_inv_natCast_pow (by positivity : (0 : ℝ) ≤ n / 2) hd.ne')
  have hfloor : r < (projectionGridSize d n : ℝ) + 1 := Nat.lt_floor_add_one r
  have hk1 : (1 : ℝ) ≤ projectionGridSize d n := by exact_mod_cast hk
  exact ⟨hk, hbudget, by linarith⟩

/-- The reciprocal cell width is controlled uniformly after flooring. -/
theorem projection_grid_inverse_width_bound {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n) :
    1 / (projectionGridSize d n : ℝ) ≤
      (2 * (2 : ℝ) ^ ((d : ℝ)⁻¹)) * (n : ℝ) ^ (-((d : ℝ)⁻¹)) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hspec := projection_grid_size_spec hd hn
  have hkreal : (0 : ℝ) < projectionGridSize d n := by exact_mod_cast hspec.1
  have hrreal : (0 : ℝ) < ((n : ℝ) / 2) ^ ((d : ℝ)⁻¹) := Real.rpow_pos_of_pos (by positivity) _
  have hi : 1 / (projectionGridSize d n : ℝ) ≤
      2 / (((n : ℝ) / 2) ^ ((d : ℝ)⁻¹)) := by
    apply (div_le_div_iff₀ hkreal hrreal).mpr
    simpa only [one_mul] using hspec.2.2
  apply hi.trans_eq
  rw [Real.div_rpow hnreal.le (by norm_num), Real.rpow_neg hnreal.le]
  field_simp

/-- A fixed, explicit coefficient for the nonparametric projection bias. -/
def gridProjectionApproximationConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  4 * (C.holderBound *
    (Real.sqrt (d : ℝ) * (2 * (2 : ℝ) ^ ((d : ℝ)⁻¹))) ^ C.smoothness) ^ 4

/-- The actual grid approximation contribution has the manuscript's
`n^(-4s/d)` dependence for the root-floor grid choice. -/
theorem projection_grid_bias_rate {d n : ℕ} (C : ModelConstants d)
    (hd : 0 < d) (hn : 2 ≤ n) :
    gridProjectionBias C (projectionGridSize d n) ≤
      gridProjectionApproximationConstant C * (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hkreal : (0 : ℝ) < projectionGridSize d n := by
    exact_mod_cast (projection_grid_size_spec hd hn).1
  have hw := mul_le_mul_of_nonneg_left (projection_grid_inverse_width_bound hd hn)
    (Real.sqrt_nonneg (d : ℝ))
  have hp := Real.rpow_le_rpow (by positivity :
    0 ≤ Real.sqrt (d : ℝ) * (1 / (projectionGridSize d n : ℝ))) hw C.smoothness_pos.le
  have hHp := mul_le_mul_of_nonneg_left hp C.holderBound_pos.le
  have hbase : 0 ≤ C.holderBound * (Real.sqrt (d : ℝ) * (1 / (projectionGridSize d n : ℝ))) ^ C.smoothness :=
    mul_nonneg C.holderBound_pos.le (Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) _)
  have hpow := pow_le_pow_left₀ hbase hHp 4
  unfold gridProjectionBias gridProjectionApproximationConstant
  apply (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
  rw [← mul_assoc (Real.sqrt (d : ℝ)), Real.mul_rpow (by positivity) (by positivity), mul_assoc,
    mul_pow]
  have hpower : (((n : ℝ) ^ (-((d : ℝ)⁻¹))) ^ C.smoothness) ^ 4 =
      (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hnreal.le]
    congr 1
    ring
  simp only [mul_pow]
  rw [hpower]
  ring

end NearlyMinimax
