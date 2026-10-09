module

public import NearlyMinimax.PairPilotBudgets
public import NearlyMinimax.PairRateAlgebra


@[expose] public section

/-! The paper's common pair-risk rate, under primitive pilot assumptions and
its original covariate-dependent conditional response model. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

/-- Proposition `prop:pair-risk`, with the universally valid floor `a=1/4`.
The displayed constant depends only on the model, pilot constant, and fixed
sample fraction. The estimator numerator is the actual observed rank-one form. -/
theorem paper_common_pair_rms {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (Cp W : ℝ)
    {n m : ℕ} (hn : 0 < n) (hm : 2 ≤ m) {c : ℝ} (hc : 0 < c)
    (hsize : c * (n : ℝ) ≤ m)
    (hp : PairPilotAssumptions θ k hk μ bar η Cp W (Cp ^ 2 * W / (n : ℝ)))
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (X : Fin m → Ξ → Observation d) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν (observationLaw θ)) (b : ℝ)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    (∫⁻ z, ENNReal.ofReal
      ((stabilizedRatio C.varianceLower C.varianceUpper (1 / 4)
        (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNumeratorKernel k hk bar η) X)
        (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNoiseKernel k hk bar η) X) z -
          θ.variance) ^ 2) ∂(μ.prod μ).prod ν) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp c (1 / 4)) *
      (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W))) := by
  have hfloor : 2 * (1 / 4 : ℝ) ≤ ∫ p, pairPilotNoiseMean θ k hk bar η p ∂μ.prod μ := by
    have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W _ hp
    norm_num only [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num]
    exact pairPilotNoiseMean_denominator_lower C θ hθ k hk μ bar η Cp _ hM hfirst
  have hr := common_pair_ratio_risk_le μ ν C θ hθ k hk bar η Cp W _ hp hm X hind hX
    b (1 / 4) (by norm_num) hresidual hfloor
  have hrate := pairRiskBudget_rate_le (k := k) (b := b) C hn hm hp.constantNonnegative hp.budgetNonnegative
    hp.lamNonnegative (pairPilotVarianceBase_nonneg θ k hk μ bar η)
    hc (by norm_num : (0 : ℝ) < 1 / 4) hsize le_rfl
    (pairPilotVarianceBase_le μ C θ hθ k hk bar η Cp W _ hp)
  have h := hr.trans (ENNReal.ofReal_mono hrate)
  have hC0 := (pairRateSquaredConstant_pos C hp.constantNonnegative hc (by norm_num : (0 : ℝ) < 1 / 4)).le
  have hR0 : 0 ≤ b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W) := by
    have ht := pairFluctuationScale_nonneg (d := d) n k
    have hW := hp.budgetNonnegative
    positivity
  have hrms := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC0 (sq_nonneg _)) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hC0, Real.sqrt_sq hR0] at hrms
  exact hrms

/-- The same paper rate for every fixed positive floor satisfying the
actual denominator-mean condition. `fieldPairAverage_integral` identifies
this mean with the mean of the displayed denominator statistic. -/
theorem paper_common_pair_rms_of_floor {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (Cp W : ℝ)
    {n m : ℕ} (hn : 0 < n) (hm : 2 ≤ m) {c : ℝ} (hc : 0 < c)
    (hsize : c * (n : ℝ) ≤ m)
    (hp : PairPilotAssumptions θ k hk μ bar η Cp W (Cp ^ 2 * W / (n : ℝ)))
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (X : Fin m → Ξ → Observation d) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν (observationLaw θ)) (b a : ℝ) (ha : 0 < a)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b)
    (hfloor : 2 * a ≤ ∫ p, pairPilotNoiseMean θ k hk bar η p ∂μ.prod μ) :
    (∫⁻ z, ENNReal.ofReal
      ((stabilizedRatio C.varianceLower C.varianceUpper a
        (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNumeratorKernel k hk bar η) X)
        (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNoiseKernel k hk bar η) X) z -
          θ.variance) ^ 2) ∂(μ.prod μ).prod ν) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp c a) *
      (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W))) := by
  have hr := common_pair_ratio_risk_le μ ν C θ hθ k hk bar η Cp W _ hp hm X hind hX
    b a ha hresidual hfloor
  have hrate := pairRiskBudget_rate_le (k := k) (b := b) C hn hm hp.constantNonnegative hp.budgetNonnegative
    hp.lamNonnegative (pairPilotVarianceBase_nonneg θ k hk μ bar η)
    hc ha hsize le_rfl
    (pairPilotVarianceBase_le μ C θ hθ k hk bar η Cp W _ hp)
  have h := hr.trans (ENNReal.ofReal_mono hrate)
  have hC0 := (pairRateSquaredConstant_pos C hp.constantNonnegative hc ha).le
  have hR0 : 0 ≤ b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W) := by
    have ht := pairFluctuationScale_nonneg (d := d) n k
    have hW := hp.budgetNonnegative
    positivity
  have hrms := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC0 (sq_nonneg _)) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hC0, Real.sqrt_sq hR0] at hrms
  exact hrms

end NearlyMinimax
