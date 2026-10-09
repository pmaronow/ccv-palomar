module

public import NearlyMinimax.PairPilotAssumptions
public import NearlyMinimax.FieldPairVariance


@[expose] public section

/-! Full two-stage variance of the paper's actual score and denominator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

def pairEvaluationCoefficient {d : ℕ} (C : ModelConstants d) (m k : ℕ) : ℝ :=
  C.densityUpper / (m : ℝ) + (k : ℝ) ^ d / (2 * (m : ℝ) * (m - 1 : ℕ))

def pairPilotVarianceBase {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) : ℝ :=
  2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
    ∫ z : Ω × (Covariate d × Covariate d), ‖η z.1 z.2‖ ^ 2
      ∂μ.prod (regularPairDesignMeasure θ k hk)

theorem pairPilotVarianceBase_nonneg {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) :
    0 ≤ pairPilotVarianceBase θ k hk μ bar η := by
  unfold pairPilotVarianceBase
  positivity

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

theorem pairPilotScoreEstimate_centered_sq_le :
    (∫ z, (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (pairPilotScoreKernel θ k hk bar η) X z -
        ∫ p, pairPilotScoreMean θ k hk bar η p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod ν) ≤
      2 * pairEvaluationCoefficient C m k *
        ((2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * responseOperatorEnergyBound C * C.densityUpper) +
      (3 / 2) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 *
        pairPilotVarianceBase θ k hk μ bar η := by
  let := observationLaw_isProbability C θ hθ
  have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp
  obtain ⟨hmean, hvar⟩ := pairPilotScoreMean_variance_le C θ hθ k hk μ bar η Cp lam hM
  have hmeas := rawModelPairScore_measurable θ k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
  have hL2 := pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hd0 : 0 ≤ (3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 *
      pairPilotVarianceBase θ k hk μ bar η := by
    have hb := pairPilotVarianceBase_nonneg θ k hk μ bar η
    have hl := hp.lamNonnegative
    positivity
  have hr := PairUStatistic.fieldPairAverage_centered_sq_le
    (π := μ.prod μ) (ν := ν) (μ := observationLaw θ)
    (G := pairPilotScoreKernel θ k hk bar η)
    (cap := C.densityUpper / (k : ℝ) ^ d) (bound := C.densityUpper) hm X hind hX
    (regularObservationLabel (d := d) k hk) (regularObservationLabel_measurable (d := d) k hk)
    hmeas hL2
    (fun p x y hxy => by simp [rawModelPairScore, pairPilotScoreKernel, pairScoreFieldKernel,
      regularObservationLabel, pairCovariates, sameLabelKernel] at hxy ⊢; exact hxy.elim)
    hkp (div_nonneg hpplus hkp.le)
    (fun i => by
      rw [regularObservationLabel_mass C θ hθ k hk i]
      exact regularGridProbability_cap C θ hθ k hk i)
    (by rw [mul_div_cancel₀ _ hkp.ne']) hd0 hmean hvar
  have he := pairPilotScoreKernel_energy_le μ C θ hθ k hk bar η Cp W lam hp
  have hE : (k : ℝ) ^ d *
      (∫ z : (Ω × Ω) × (Observation d × Observation d),
        pairPilotScoreKernel θ k hk bar η z.1 z.2 ^ 2
          ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * responseOperatorEnergyBound C * C.densityUpper := by
    apply (mul_le_mul_of_nonneg_left he hkp.le).trans_eq
    field_simp
  have heval : 0 ≤ pairEvaluationCoefficient C m k := by unfold pairEvaluationCoefficient; positivity
  apply hr.trans
  change 2 * pairEvaluationCoefficient C m k * _ + 2 *
    ((3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 * pairPilotVarianceBase θ k hk μ bar η) ≤ _
  have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * pairEvaluationCoefficient C m k)
  nlinarith

theorem pairPilotNoiseEstimate_centered_sq_le :
    (∫ z, (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (pairPilotNoiseKernel k hk bar η) X z -
        ∫ p, pairPilotNoiseMean θ k hk bar η p ∂μ.prod μ) ^ 2 ∂(μ.prod μ).prod ν) ≤
      8 * pairEvaluationCoefficient C m k *
        ((2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * C.densityUpper) +
      6 * lam * pairPilotVarianceBase θ k hk μ bar η := by
  let := observationLaw_isProbability C θ hθ
  have hM := pairPilotAssumptions_meanConditions μ C θ hθ k hk bar η Cp W lam hp
  obtain ⟨hmean, hvar⟩ := pairPilotNoiseMean_variance_le C θ hθ k hk μ bar η Cp lam hM
  have hmeas := rawModelPairNoise_measurable k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
  have hL2 := pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hd0 : 0 ≤ 3 * lam * pairPilotVarianceBase θ k hk μ bar η := by
    have hb := pairPilotVarianceBase_nonneg θ k hk μ bar η
    have hl := hp.lamNonnegative
    positivity
  have hr := PairUStatistic.fieldPairAverage_centered_sq_le
    (π := μ.prod μ) (ν := ν) (μ := observationLaw θ)
    (G := pairPilotNoiseKernel k hk bar η)
    (cap := C.densityUpper / (k : ℝ) ^ d) (bound := C.densityUpper) hm X hind hX
    (regularObservationLabel (d := d) k hk) (regularObservationLabel_measurable (d := d) k hk)
    hmeas hL2
    (fun p x y hxy => by simp [rawModelPairNoise, pairPilotNoiseKernel, pairNoiseFieldKernel,
      regularObservationLabel, pairCovariates, sameLabelKernel] at hxy ⊢; exact hxy.elim)
    hkp (div_nonneg hpplus hkp.le)
    (fun i => by
      rw [regularObservationLabel_mass C θ hθ k hk i]
      exact regularGridProbability_cap C θ hθ k hk i)
    (by rw [mul_div_cancel₀ _ hkp.ne']) hd0 hmean hvar
  have he := pairPilotNoiseKernel_energy_le μ C θ hθ k hk bar η Cp W lam hp
  have hE : (k : ℝ) ^ d *
      (∫ z : (Ω × Ω) × (Observation d × Observation d),
        pairPilotNoiseKernel k hk bar η z.1 z.2 ^ 2
          ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      4 * (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * C.densityUpper := by
    apply (mul_le_mul_of_nonneg_left he hkp.le).trans_eq
    field_simp
  have heval : 0 ≤ pairEvaluationCoefficient C m k := by unfold pairEvaluationCoefficient; positivity
  apply hr.trans
  change 2 * pairEvaluationCoefficient C m k * _ + 2 *
    (3 * lam * pairPilotVarianceBase θ k hk μ bar η) ≤ _
  have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * pairEvaluationCoefficient C m k)
  nlinarith

end
end NearlyMinimax
