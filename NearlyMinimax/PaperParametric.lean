module

public import NearlyMinimax.ProjectionUpper
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.PaperGoals


@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace NearlyMinimax

/-- The displayed projection RMS rate, in maximum form. -/
def projectionRMSScale {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℝ :=
  max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(2 * C.smoothness / d)))

theorem projectionUpperConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < projectionUpperConstant C := by
  have hV : 0 < C.varianceUpper := C.varianceLower_pos.trans C.variance_interval
  have hm : 0 ≤ max C.fourthBound (2 * C.varianceUpper ^ 2) :=
    (by positivity : 0 ≤ 2 * C.varianceUpper ^ 2).trans (le_max_right _ _)
  have hG : 0 < gridProjectionConstant C := by
    unfold gridProjectionConstant
    positivity
  exact hG.trans_le (projection_upper_constant_bounds C).1

/-- Taking the square root of the proved projection MSE rate gives its
exact maximum-form RMS rate for any extended-valued risk. -/
theorem projection_rms_bound_of_mse {d n : ℕ} (C : ModelConstants d) (hn : 0 < n)
    {r : ℝ≥0∞} (hr : r ≤ ENNReal.ofReal (projectionUpperConstant C *
      (1 / (n : ℝ) + (n : ℝ) ^ (-(4 * C.smoothness / d))))) :
    r ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal
      (Real.sqrt (2 * projectionUpperConstant C) * projectionRMSScale C n) := by
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
  have hMSE := hr.trans (ENNReal.ofReal_le_ofReal hreal)
  apply (ENNReal.rpow_le_rpow hMSE (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 2 * projectionUpperConstant C * m ^ 2) (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity : 0 ≤ 2 * projectionUpperConstant C),
    Real.sqrt_sq hm0]
  rfl

/-- A concrete clipped Borel estimator attains the worst-case projection
RMS bound, expressed as the supremum of the actual model's L² errors. -/
theorem projection_estimator_l2_bound {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    (⨆ θ : {θ : RegressionParameter d // Admissible C θ},
      eLpNorm (fun z => (clippedEstimator C (projectionUpperEstimator C n)).val z - θ.val.variance)
        2 (sampleLaw θ.val n)) ≤
    ENNReal.ofReal (Real.sqrt (2 * projectionUpperConstant C) * projectionRMSScale C n) := by
  have hMSE := (clippedEstimator_worstCaseRisk_le C (projectionUpperEstimator C n)).trans
    (projection_upper_estimator_risk C hn)
  have hRMS := projection_rms_bound_of_mse C hn hMSE
  let φ := ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)
  have heq : worstCaseRisk C (clippedEstimator C (projectionUpperEstimator C n)) ^ (1 / 2 : ℝ) =
      ⨆ θ : {θ : RegressionParameter d // Admissible C θ},
        meanSquaredRisk (clippedEstimator C (projectionUpperEstimator C n)) θ.val ^ (1 / 2 : ℝ) := by
    exact φ.map_iSup _
  rw [heq] at hRMS
  simpa only [meanSquaredRisk_rpow_eq_eLpNorm] using hRMS

/-- The numerical projection constant is independent of the open extension domain. -/
theorem projectionUpperConstant_withDomain {d : ℕ} (C : ModelConstants d)
    (U : ExtensionDomain d) : projectionUpperConstant (C.withDomain U) = projectionUpperConstant C := rfl

/-- Manuscript `lem:projection-upper`: a Borel estimator with the stated
sum-form worst-case L² bound for every sample size. The constant is uniform
over all permitted open extension domains. -/
theorem paper_projection_upper {d : ℕ} (C : ModelConstants d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (U : ExtensionDomain d) (n : ℕ), 1 ≤ n →
      ∃ T : Estimator d n,
        (⨆ θ : {θ : RegressionParameter d // Admissible (C.withDomain U) θ},
          eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ≤
        ENNReal.ofReal (A * ((n : ℝ) ^ (-(1 / 2 : ℝ)) +
          (n : ℝ) ^ (-(2 * C.smoothness / d)))) := by
  let A := Real.sqrt (2 * projectionUpperConstant C)
  have hA : 0 < A := Real.sqrt_pos.mpr (mul_pos (by norm_num) (projectionUpperConstant_pos C))
  refine ⟨A, hA, ?_⟩
  intro U n hn
  refine ⟨clippedEstimator (C.withDomain U) (projectionUpperEstimator (C.withDomain U) n), ?_⟩
  have hbound := projection_estimator_l2_bound (C.withDomain U) (by omega : 0 < n)
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  change A * max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(2 * C.smoothness / d))) ≤ _
  apply mul_le_mul_of_nonneg_left _ hA.le
  exact max_le_iff.mpr ⟨le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    le_add_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)⟩

/-- Manuscript `thm:parametric`, proved against the original statistical
class by combining the actual projection estimator and constructed
ternary two-point submodel. -/
theorem paper_parametric {d : ℕ} (C : ModelConstants d) : ParametricClaim C := by
  intro hs hparametric
  obtain ⟨c, hc, hlower⟩ := parametric_minimax_lower C
  let A := max (Real.sqrt (2 * projectionUpperConstant C)) (max 1 c⁻¹)
  have hA1 : (1 : ℝ) ≤ A := (le_max_left 1 c⁻¹).trans (le_max_right _ _)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hAcinv : c⁻¹ ≤ A := (le_max_right 1 c⁻¹).trans (le_max_right _ _)
  have hAupper : Real.sqrt (2 * projectionUpperConstant C) ≤ A := le_max_left _ _
  have hAc : A⁻¹ ≤ c := by
    calc
      A⁻¹ ≤ (c⁻¹)⁻¹ := (inv_le_inv₀ hA (inv_pos.mpr hc)).mpr hAcinv
      _ = c := inv_inv c
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hscale := Real.rpow_nonneg hn0 (-(1 / 2 : ℝ))
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hlower n hn)
  · exact (minimax_rms_projection_parametric_upper C (by omega) hparametric).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAupper hscale))

/-- The all-`n` two-sided maximum-form parametric bracket. -/
theorem paper_parametric_max_root_bracket {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (hparametric : (d : ℝ) ≤ 4 * C.smoothness) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * projectionRMSScale C n) ≤ minimaxRMS C n ∧
      minimaxRMS C n ≤ ENNReal.ofReal (A * projectionRMSScale C n) := by
  obtain ⟨A, hA, hbound⟩ := paper_parametric C hs hparametric
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hdreal : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(2 * C.smoothness / d) ≤ -(1 / 2 : ℝ) := by
    apply neg_le_neg
    apply (le_div_iff₀ hdreal).mpr
    nlinarith [hparametric]
  have hp := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  simpa only [projectionRMSScale, max_eq_left hp] using hbound n hn

end NearlyMinimax
