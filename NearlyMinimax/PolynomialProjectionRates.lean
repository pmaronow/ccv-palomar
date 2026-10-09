module

public import NearlyMinimax.PolynomialGridProjection
public import NearlyMinimax.ProjectionGridChoice


@[expose] public section

open scoped ENNReal
noncomputable section
namespace NearlyMinimax

/-- Number of rectangular monomial features per grid cell. -/
def polynomialFeatureCount {d : ℕ} (C : ModelConstants d) : ℕ := (C.order + 1) ^ d

theorem polynomialFeatureCount_pos {d : ℕ} (C : ModelConstants d) :
    0 < polynomialFeatureCount C := by
  unfold polynomialFeatureCount
  positivity

/-- The actual root-floor grid uses half the sample as its feature budget. -/
def polynomialProjectionGridSize {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℕ :=
  ⌊((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)⌋₊

theorem polynomial_projection_grid_size_spec {d n : ℕ} (C : ModelConstants d)
    (hn : 2 * polynomialFeatureCount C ≤ n) :
    0 < polynomialProjectionGridSize C n ∧
    (polynomialProjectionGridSize C n : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2 ∧
    ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹) ≤
      2 * polynomialProjectionGridSize C n := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
  have hqreal : (0 : ℝ) < polynomialFeatureCount C := by exact_mod_cast polynomialFeatureCount_pos C
  have hnreal : 2 * (polynomialFeatureCount C : ℝ) ≤ n := by exact_mod_cast hn
  let r := ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)
  have hb1 : (1 : ℝ) ≤ n / (2 * polynomialFeatureCount C) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul] using hnreal
  have hr1 : 1 ≤ r := Real.one_le_rpow hb1 (inv_nonneg.mpr hdreal.le)
  have hk : 0 < polynomialProjectionGridSize C n := Nat.floor_pos.mpr hr1
  have hkle : (polynomialProjectionGridSize C n : ℝ) ≤ r := Nat.floor_le (by positivity)
  have hroot : r ^ d = (n : ℝ) / (2 * polynomialFeatureCount C) :=
    Real.rpow_inv_natCast_pow (by positivity) C.dimension_pos.ne'
  have hbudget := (pow_le_pow_left₀ (Nat.cast_nonneg _) hkle d).trans_eq hroot
  have hbudget' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * polynomialFeatureCount C)).mp hbudget
  have hfeature : ((C.order + 1 : ℕ) : ℝ) ^ d = polynomialFeatureCount C := by
    simp only [polynomialFeatureCount, Nat.cast_pow]
  have hcolumns : (polynomialProjectionGridSize C n : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2 := by
    rw [hfeature]
    nlinarith
  have hfloor : r < (polynomialProjectionGridSize C n : ℝ) + 1 := Nat.lt_floor_add_one r
  have hk1 : (1 : ℝ) ≤ polynomialProjectionGridSize C n := by exact_mod_cast hk
  exact ⟨hk, hcolumns, by linarith⟩

/-- Floor rounding changes inverse cell width by a fixed model factor. -/
theorem polynomial_projection_grid_inverse_width_bound {d n : ℕ} (C : ModelConstants d)
    (hn : 2 * polynomialFeatureCount C ≤ n) :
    1 / (polynomialProjectionGridSize C n : ℝ) ≤
      (2 * (2 * polynomialFeatureCount C : ℝ) ^ ((d : ℝ)⁻¹)) *
        (n : ℝ) ^ (-((d : ℝ)⁻¹)) := by
  have hqreal : (0 : ℝ) < polynomialFeatureCount C := by exact_mod_cast polynomialFeatureCount_pos C
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by have := polynomialFeatureCount_pos C; omega : 0 < 2 * polynomialFeatureCount C) hn)
  have hspec := polynomial_projection_grid_size_spec C hn
  have hkreal : (0 : ℝ) < polynomialProjectionGridSize C n := by exact_mod_cast hspec.1
  have hrreal : (0 : ℝ) < ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hi : 1 / (polynomialProjectionGridSize C n : ℝ) ≤
      2 / (((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)) := by
    apply (div_le_div_iff₀ hkreal hrreal).mpr
    simpa only [one_mul] using hspec.2.2
  apply hi.trans_eq
  rw [Real.div_rpow hnreal.le (by positivity), Real.rpow_neg hnreal.le]
  field_simp

/-- Explicit full-smoothness approximation constant, independent of sample size. -/
def polynomialProjectionApproximationConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  4 * (taylorErrorFactor C * C.holderBound *
    (2 * (2 * polynomialFeatureCount C : ℝ) ^ ((d : ℝ)⁻¹)) ^ C.smoothness) ^ 4

/-- The constructed full-order projection bias has rate `n^(-4s/d)`. -/
theorem polynomial_projection_grid_bias_rate {d n : ℕ} (C : ModelConstants d)
    (hn : 2 * polynomialFeatureCount C ≤ n) :
    polynomialGridBias C (polynomialProjectionGridSize C n) ≤
      polynomialProjectionApproximationConstant C * (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by have := polynomialFeatureCount_pos C; omega : 0 < 2 * polynomialFeatureCount C) hn)
  have hkreal : (0 : ℝ) < polynomialProjectionGridSize C n := by
    exact_mod_cast (polynomial_projection_grid_size_spec C hn).1
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / (polynomialProjectionGridSize C n : ℝ))
    (polynomial_projection_grid_inverse_width_bound C hn) C.smoothness_pos.le
  have hcoef : 0 ≤ taylorErrorFactor C * C.holderBound :=
    mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le
  have hHp := mul_le_mul_of_nonneg_left hp hcoef
  have hbase : 0 ≤ taylorErrorFactor C * C.holderBound *
      (1 / (polynomialProjectionGridSize C n : ℝ)) ^ C.smoothness :=
    mul_nonneg hcoef (Real.rpow_nonneg (by positivity) _)
  have hpow := pow_le_pow_left₀ hbase hHp 4
  unfold polynomialGridBias polynomialProjectionApproximationConstant
  apply (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have hpower : (((n : ℝ) ^ (-((d : ℝ)⁻¹))) ^ C.smoothness) ^ 4 =
      (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hnreal.le]
    congr 1
    ring
  simp only [mul_pow]
  rw [hpower]
  ring

end NearlyMinimax
