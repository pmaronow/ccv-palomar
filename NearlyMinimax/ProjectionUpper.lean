module

public import NearlyMinimax.ProjectionStatisticalTransfer
public import NearlyMinimax.PolynomialProjectionRates


@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace NearlyMinimax

/-- A single finite model constant for all sample sizes, including the
small-sample fallback. -/
def projectionUpperConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  gridProjectionConstant C + polynomialProjectionApproximationConstant C +
    2 * polynomialFeatureCount C * (C.varianceUpper - C.varianceLower) ^ 2

theorem polynomialProjectionApproximationConstant_nonneg {d : ℕ} (C : ModelConstants d) :
    0 ≤ polynomialProjectionApproximationConstant C := by
  unfold polynomialProjectionApproximationConstant
  positivity

theorem projectionUpperConstant_nonneg {d : ℕ} (C : ModelConstants d) :
    0 ≤ projectionUpperConstant C := by
  have hg := gridProjectionConstant_nonneg C
  have ha := polynomialProjectionApproximationConstant_nonneg C
  unfold projectionUpperConstant
  positivity

theorem projection_upper_constant_bounds {d : ℕ} (C : ModelConstants d) :
    gridProjectionConstant C ≤ projectionUpperConstant C ∧
    polynomialProjectionApproximationConstant C ≤ projectionUpperConstant C ∧
    2 * polynomialFeatureCount C * (C.varianceUpper - C.varianceLower) ^ 2 ≤
      projectionUpperConstant C := by
  have hg := gridProjectionConstant_nonneg C
  have ha := polynomialProjectionApproximationConstant_nonneg C
  have hf : 0 ≤ 2 * (polynomialFeatureCount C : ℝ) * (C.varianceUpper - C.varianceLower) ^ 2 := by positivity
  unfold projectionUpperConstant
  constructor
  · linarith
  constructor <;> linarith

/-- Explicit Borel estimator: the polynomial grid when its feature budget
fits, and the admissible lower variance endpoint for smaller samples. -/
def projectionUpperEstimator {d : ℕ} (C : ModelConstants d) (n : ℕ) : Estimator d n :=
  if hn : 2 * polynomialFeatureCount C ≤ n then
    polynomialGridEstimator C n (polynomialProjectionGridSize C n)
      (polynomial_projection_grid_size_spec C hn).1
  else constantEstimator d n C.varianceLower

/-- Uniform worst-case risk of the constructed estimator, against the
original iid model, in every smoothness order and every positive sample size. -/
theorem projection_upper_estimator_risk {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    worstCaseRisk C (projectionUpperEstimator C n) ≤
      ENNReal.ofReal (projectionUpperConstant C *
        (1 / (n : ℝ) + (n : ℝ) ^ (-(4 * C.smoothness / d)))) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hbounds := projection_upper_constant_bounds C
  have hK := projectionUpperConstant_nonneg C
  by_cases hbudget : 2 * polynomialFeatureCount C ≤ n
  · rw [projectionUpperEstimator, dite_eq_left hbudget]
    have hspec := polynomial_projection_grid_size_spec C hbudget
    have hbase := polynomial_grid_worst_case_risk_bound C (polynomialProjectionGridSize C n)
      hspec.1 hn hspec.2.1
    apply hbase.trans
    apply ENNReal.ofReal_le_ofReal
    have hb := polynomial_projection_grid_bias_rate C hbudget
    have hG := mul_le_mul_of_nonneg_right hbounds.1 (by positivity : 0 ≤ (n : ℝ)⁻¹)
    have hA := mul_le_mul_of_nonneg_right hbounds.2.1
      (Real.rpow_nonneg hnreal.le (-(4 * C.smoothness / d)))
    calc
      _ ≤ gridProjectionConstant C / n + polynomialProjectionApproximationConstant C *
          (n : ℝ) ^ (-(4 * C.smoothness / d)) := add_le_add le_rfl hb
      _ ≤ projectionUpperConstant C / n + projectionUpperConstant C *
          (n : ℝ) ^ (-(4 * C.smoothness / d)) :=
        add_le_add (div_le_div_of_nonneg_right hbounds.1 (Nat.cast_nonneg n)) hA
      _ = _ := by ring
  · rw [projectionUpperEstimator, dite_eq_right hbudget]
    unfold worstCaseRisk
    apply iSup_le
    intro θ
    apply (constantEstimator_risk_bound C θ.val θ.property).trans
    apply ENNReal.ofReal_le_ofReal
    have hsmall : (n : ℝ) ≤ 2 * polynomialFeatureCount C := by
      exact_mod_cast (by omega : n ≤ 2 * polynomialFeatureCount C)
    have hdiam : (C.varianceUpper - C.varianceLower) ^ 2 ≤ projectionUpperConstant C / n := by
      apply (le_div_iff₀ hnreal).mpr
      have hm := mul_le_mul_of_nonneg_left hsmall (sq_nonneg (C.varianceUpper - C.varianceLower))
      nlinarith [hbounds.2.2]
    have hrate : 0 ≤ (n : ℝ) ^ (-(4 * C.smoothness / d)) := Real.rpow_nonneg hnreal.le _
    calc
      _ ≤ projectionUpperConstant C / n := hdiam
      _ ≤ _ := by rw [div_eq_mul_inv, one_div]; nlinarith [mul_nonneg hK hrate]

/-- The polynomial-projection upper bound for the paper's original
minimax MSE: `C (n⁻¹ + n^(-4s/d))`. Every statistical and approximation
hypothesis is supplied by the original admissibility definition. -/
theorem minimax_projection_upper {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    minimaxRisk C n ≤ ENNReal.ofReal (projectionUpperConstant C *
      (1 / (n : ℝ) + (n : ℝ) ^ (-(4 * C.smoothness / d)))) :=
  (minimaxRisk_le_worstCaseRisk C _).trans (projection_upper_estimator_risk C hn)

/-- In the parametric smoothness regime, the actual minimax MSE is at
most a fixed constant divided by the sample size. -/
theorem minimax_projection_parametric_upper {d n : ℕ} (C : ModelConstants d)
    (hn : 0 < n) (hparametric : (d : ℝ) ≤ 4 * C.smoothness) :
    minimaxRisk C n ≤ ENNReal.ofReal (2 * projectionUpperConstant C / n) := by
  apply (minimax_projection_upper C hn).trans
  apply ENNReal.ofReal_le_ofReal
  have hdreal : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(4 * C.smoothness / d) ≤ (-1 : ℝ) := by
    apply neg_le_neg
    apply (le_div_iff₀ hdreal).mpr
    simpa only [one_mul] using hparametric
  have hp := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  rw [Real.rpow_neg_one] at hp
  have hK := projectionUpperConstant_nonneg C
  calc
    _ ≤ projectionUpperConstant C * (1 / (n : ℝ) + (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hp) hK
    _ = _ := by rw [one_div]; ring


/-- The projection upper bound in the paper's root mean square scale,
with the maximum of parametric and smoothness contributions. -/
theorem minimax_rms_projection_upper {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    minimaxRMS C n ≤ ENNReal.ofReal (Real.sqrt (2 * projectionUpperConstant C) *
      max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(2 * C.smoothness / d)))) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hK := projectionUpperConstant_nonneg C
  let a := (n : ℝ) ^ (-(1 / 2 : ℝ))
  let b := (n : ℝ) ^ (-(2 * C.smoothness / d))
  let m := max a b
  have ha0 : 0 ≤ a := Real.rpow_nonneg hnreal.le _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hnreal.le _
  have hm0 : 0 ≤ m := ha0.trans (le_max_left a b)
  have ha : a ^ 2 = 1 / (n : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hnreal.le]
    norm_num
    simp only [Real.rpow_neg_one]
  have hb : b ^ 2 = (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast hnreal.le]
    congr 1
    ring
  have ham : a ^ 2 ≤ m ^ 2 := (sq_le_sq₀ ha0 hm0).mpr (le_max_left a b)
  have hbm : b ^ 2 ≤ m ^ 2 := (sq_le_sq₀ hb0 hm0).mpr (le_max_right a b)
  have hreal : projectionUpperConstant C *
      (1 / (n : ℝ) + (n : ℝ) ^ (-(4 * C.smoothness / d))) ≤
      2 * projectionUpperConstant C * m ^ 2 := by
    rw [← ha, ← hb]
    have hm := mul_le_mul_of_nonneg_left (add_le_add ham hbm) hK
    nlinarith
  have hMSE := (minimax_projection_upper C hn).trans (ENNReal.ofReal_le_ofReal hreal)
  unfold minimaxRMS
  apply (ENNReal.rpow_le_rpow hMSE (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 2 * projectionUpperConstant C * m ^ 2) (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity : 0 ≤ 2 * projectionUpperConstant C),
    Real.sqrt_sq hm0]

theorem minimax_rms_projection_parametric_upper {d n : ℕ} (C : ModelConstants d)
    (hn : 0 < n) (hparametric : (d : ℝ) ≤ 4 * C.smoothness) :
    minimaxRMS C n ≤ ENNReal.ofReal (Real.sqrt (2 * projectionUpperConstant C) *
      (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(2 * C.smoothness / d) ≤ -(1 / 2 : ℝ) := by
    apply neg_le_neg
    apply (le_div_iff₀ hdreal).mpr
    nlinarith [hparametric]
  have hp := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  simpa only [max_eq_left hp] using minimax_rms_projection_upper C hn

end NearlyMinimax
