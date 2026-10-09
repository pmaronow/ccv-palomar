module

public import NearlyMinimax.PairEvaluationVariance
public import NearlyMinimax.PairStatisticAlgebra
public import NearlyMinimax.StabilizedRatioRisk


@[expose] public section

/-! Risk of the actual independent-pilot ratio estimator, derived only from
primitive pilot moment and universal linear-test bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

def pairRiskBudget {d : ℕ} (C : ModelConstants d) (m k : ℕ)
    (Cp W lam B b a : ℝ) : ℝ :=
  (2 / a ^ 2) *
    (4 * pairEvaluationCoefficient C m k *
      ((2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * responseOperatorEnergyBound C * C.densityUpper) +
    3 * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * B +
    2 * ((C.densityUpper / 2) * b ^ 2) ^ 2 +
    C.varianceUpper ^ 2 *
      (8 * pairEvaluationCoefficient C m k *
        ((2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * C.densityUpper) + 6 * lam * B))

theorem integral_sq_le_twice_centered {Z : Type*} [MeasurableSpace Z]
    (ρ : Measure Z) [IsProbabilityMeasure ρ] {S : Z → ℝ} (hS : MemLp S 2 ρ) (c : ℝ) :
    (∫ z, S z ^ 2 ∂ρ) ≤ 2 * (∫ z, (S z - c) ^ 2 ∂ρ) + 2 * c ^ 2 := by
  have hc : MemLp (fun z => S z - c) 2 ρ := hS.sub (memLp_const c)
  have hiR : Integrable (fun z => 2 * (S z - c) ^ 2 + 2 * c ^ 2) ρ :=
    (hc.integrable_sq.const_mul 2).add (integrable_const (2 * c ^ 2))
  have h : (∫ z, S z ^ 2 ∂ρ) ≤ ∫ z, 2 * (S z - c) ^ 2 + 2 * c ^ 2 ∂ρ :=
    integral_mono hS.integrable_sq hiR (fun z => by nlinarith [sq_nonneg (S z - 2 * c)])
  rw [integral_add (hc.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul] at h
  simpa using h

section
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
variable {m : ℕ} (hm : 2 ≤ m) (X : Fin m → Ξ → Observation d)
variable (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν (observationLaw θ))
include hθ hp hm hind hX

theorem common_pair_denominator_mean_lower
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1) :
    (1 / 2 : ℝ) ≤ ∫ z, PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (pairPilotNoiseKernel k hk bar η) X z ∂(μ.prod μ).prod ν := by
  let := observationLaw_isProbability C θ hθ
  have hmc := pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp
  rw [PairUStatistic.fieldPairAverage_integral (G := pairPilotNoiseKernel k hk bar η) hm ((k : ℝ) ^ d)
    (rawModelPairNoise_measurable k hk hmc)
    (pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp) X hind hX]
  exact pairPilotNoiseMean_denominator_lower C θ hθ k hk μ bar η Cp lam
    (pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp) hfirst

/-- The numerator uses the observed rank-one response form, and therefore
its definition is independent of the unknown variance. -/
theorem common_pair_numerator_denominator_memLp :
    MemLp (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (pairPilotNumeratorKernel k hk bar η) X) 2 ((μ.prod μ).prod ν) ∧
    MemLp (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (pairPilotNoiseKernel k hk bar η) X) 2 ((μ.prod μ).prod ν) := by
  let := observationLaw_isProbability C θ hθ
  have hS := PairUStatistic.fieldPairAverage_memLp ((k : ℝ) ^ d)
    (pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp) X hind hX
  have hD := PairUStatistic.fieldPairAverage_memLp ((k : ℝ) ^ d)
    (pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp) X hind hX
  refine ⟨?_, hD⟩
  have he : PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (pairPilotNumeratorKernel k hk bar η) X =
      (fun z => PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
        (pairPilotScoreKernel θ k hk bar η) X z + θ.variance *
          PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNoiseKernel k hk bar η) X z) := by
    funext z
    rw [pairPilotNumeratorKernel_eq_score_add_noise θ]
    exact PairUStatistic.fieldPairAverage_add_smul _ _ _ _ _ _ _
  rw [he]
  exact hS.add (hD.const_mul θ.variance)

/-- Extended-real MSE of the actual floored and clipped ratio. All moments,
conditional means, denominator positivity, and covariance bounds are derived. -/
theorem common_pair_ratio_risk_le (b a : ℝ) (ha : 0 < a)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b)
    (hfloor : 2 * a ≤ ∫ p, pairPilotNoiseMean θ k hk bar η p ∂μ.prod μ) :
    (∫⁻ z, ENNReal.ofReal
      ((stabilizedRatio C.varianceLower C.varianceUpper a
        (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNumeratorKernel k hk bar η) X)
        (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNoiseKernel k hk bar η) X) z -
          θ.variance) ^ 2) ∂(μ.prod μ).prod ν) ≤
    ENNReal.ofReal (pairRiskBudget C m k Cp W lam
      (pairPilotVarianceBase θ k hk μ bar η) b a) := by
  let := observationLaw_isProbability C θ hθ
  let S := PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotScoreKernel θ k hk bar η) X
  let D := PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNoiseKernel k hk bar η) X
  let N := PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (pairPilotNumeratorKernel k hk bar η) X
  have hmc := pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp
  have hmS : Measurable S := PairUStatistic.fieldPairAverage_measurable _ _
    (rawModelPairScore_measurable θ k hk hmc) X (fun i => (hX i).measurable)
  have hmD : Measurable D := PairUStatistic.fieldPairAverage_measurable _ _
    (rawModelPairNoise_measurable k hk hmc) X (fun i => (hX i).measurable)
  have hS : MemLp S 2 ((μ.prod μ).prod ν) := PairUStatistic.fieldPairAverage_memLp _
    (pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp) X hind hX
  have hD : MemLp D 2 ((μ.prod μ).prod ν) := PairUStatistic.fieldPairAverage_memLp _
    (pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp) X hind hX
  have he : N = fun z => S z + θ.variance * D z := by
    funext z
    dsimp [N, S, D]
    rw [pairPilotNumeratorKernel_eq_score_add_noise θ]
    exact PairUStatistic.fieldPairAverage_add_smul _ _ _ _ _ _ _
  have hmN : Measurable N := by rw [he]; exact hmS.add (hmD.const_mul _)
  have hdif : (fun z => N z - θ.variance * D z) = S := by
    rw [he]
    funext z
    ring
  have hgap : MemLp (fun z => N z - θ.variance * D z) 2 ((μ.prod μ).prod ν) := by rw [hdif]; exact hS
  have hvlo := hθ.2.2.2.2.2.1
  have hvhi := hθ.2.2.2.2.2.2.1
  have hr := stabilized_ratio_lintegral_mse_le ((μ.prod μ).prod ν) hmN hmD hgap hD
    ha hvlo hvhi (C.varianceLower_pos.le.trans hvlo) hfloor
  have hpoint : ∀ z, N z - θ.variance * D z = S z := fun z => congrFun hdif z
  simp_rw [hpoint] at hr
  have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp
  have hb := pairPilotScoreMean_abs_bias_le C θ hθ k hk μ bar η Cp lam hM b hresidual
  have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hb2
  have hSv := pairPilotScoreEstimate_centered_sq_le μ ν C θ hθ k hk bar η Cp W lam hp hm X hind hX
  have hDv := pairPilotNoiseEstimate_centered_sq_le μ ν C θ hθ k hk bar η Cp W lam hp hm X hind hX
  have hSb := integral_sq_le_twice_centered ((μ.prod μ).prod ν) hS
    (∫ p, pairPilotScoreMean θ k hk bar η p ∂μ.prod μ)
  apply hr.trans
  apply ENNReal.ofReal_mono
  unfold pairRiskBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 / a ^ 2)
  apply add_le_add
  · change (∫ z, S z ^ 2 ∂(μ.prod μ).prod ν) ≤ _
    nlinarith
  · exact mul_le_mul_of_nonneg_left hDv (sq_nonneg _)

end
end NearlyMinimax
