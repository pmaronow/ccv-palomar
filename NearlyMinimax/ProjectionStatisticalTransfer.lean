module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ProjectionStatistical
public import NearlyMinimax.PolynomialGridProjection


@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
namespace NearlyMinimax

/-- Actual iid-sample risk of the order-zero regular-grid estimator,
including conditional-law identification and averaging over random design. -/
theorem regular_grid_sample_risk_bound {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (horder : C.order = 0)
    (k : ℕ) (hk : 0 < k) (hn : 0 < n) (hcolumns : (k : ℝ) ^ d ≤ (n : ℝ) / 2) :
    meanSquaredRisk (regularGridEstimator d n k hk) θ ≤
      ENNReal.ofReal (gridProjectionConstant C / n + gridProjectionBias C k) := by
  letI := designLaw_isProbability C θ hθ
  letI : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => designLaw θ)))
  rw [meanSquaredRisk_conditioning C _ θ hθ]
  have hconditional : ∀ᵐ x ∂designVectorLaw θ n,
      (∫⁻ u, ENNReal.ofReal
        (((regularGridEstimator d n k hk).val (samplesFromDesignErrors θ (x, u)) - θ.variance) ^ 2)
        ∂conditionalErrorLaw θ x) ≤
      ENNReal.ofReal (gridProjectionConstant C / n + gridProjectionBias C k) := by
    filter_upwards [admissible_conditional_error_facts C θ hθ n] with x hx
    obtain ⟨hcube, hε, hind, hmean, hsecond, hfourth⟩ := hx
    exact regular_grid_conditional_lintegral_bound C θ hθ horder k hk hn hcolumns
      x hcube (conditionalErrorLaw θ x) (fun i u => u i) hε hind hmean hsecond hfourth
  exact (lintegral_mono_ae hconditional).trans_eq (by simp)

theorem regular_grid_worst_case_risk_bound {d n : ℕ} (C : ModelConstants d)
    (horder : C.order = 0) (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d ≤ (n : ℝ) / 2) :
    worstCaseRisk C (regularGridEstimator d n k hk) ≤
      ENNReal.ofReal (gridProjectionConstant C / n + gridProjectionBias C k) := by
  unfold worstCaseRisk
  exact iSup_le fun θ => regular_grid_sample_risk_bound C θ.val θ.property horder k hk hn hcolumns

theorem regular_grid_minimax_risk_bound {d n : ℕ} (C : ModelConstants d)
    (horder : C.order = 0) (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d ≤ (n : ℝ) / 2) :
    minimaxRisk C n ≤ ENNReal.ofReal (gridProjectionConstant C / n + gridProjectionBias C k) :=
  (minimaxRisk_le_worstCaseRisk C _).trans
    (regular_grid_worst_case_risk_bound C horder k hk hn hcolumns)

/-- The actual iid-sample polynomial-projection risk upper bound in
all smoothness orders. No conditional independence or risk identity is assumed. -/
theorem polynomial_grid_sample_risk_bound {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2) :
    meanSquaredRisk (polynomialGridEstimator C n k hk) θ ≤
      ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := by
  letI := designLaw_isProbability C θ hθ
  letI : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => designLaw θ)))
  rw [meanSquaredRisk_conditioning C _ θ hθ]
  have hconditional : ∀ᵐ x ∂designVectorLaw θ n,
      (∫⁻ u, ENNReal.ofReal
        (((polynomialGridEstimator C n k hk).val (samplesFromDesignErrors θ (x, u)) - θ.variance) ^ 2)
        ∂conditionalErrorLaw θ x) ≤
      ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := by
    filter_upwards [admissible_conditional_error_facts C θ hθ n] with x hx
    obtain ⟨hcube, hε, hind, hmean, hsecond, hfourth⟩ := hx
    exact polynomial_grid_conditional_lintegral_bound C θ hθ k hk hn hcolumns
      x hcube (conditionalErrorLaw θ x) (fun i u => u i) hε hind hmean hsecond hfourth
  exact (lintegral_mono_ae hconditional).trans_eq (by simp)

theorem polynomial_grid_worst_case_risk_bound {d n : ℕ} (C : ModelConstants d)
    (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2) :
    worstCaseRisk C (polynomialGridEstimator C n k hk) ≤
      ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := by
  unfold worstCaseRisk
  exact iSup_le fun θ => polynomial_grid_sample_risk_bound C θ.val θ.property k hk hn hcolumns

/-- The original minimax definition is bounded by a concrete Borel
polynomial-grid estimator's proved worst-case risk. -/
theorem polynomial_grid_minimax_risk_bound {d n : ℕ} (C : ModelConstants d)
    (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2) :
    minimaxRisk C n ≤ ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) :=
  (minimaxRisk_le_worstCaseRisk C _).trans
    (polynomial_grid_worst_case_risk_bound C k hk hn hcolumns)

end NearlyMinimax
