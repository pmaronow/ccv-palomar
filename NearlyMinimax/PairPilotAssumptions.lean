module

public import NearlyMinimax.PairNoiseEvaluation
public import NearlyMinimax.PairPilotMean
public import NearlyMinimax.PilotTotalMoments
public import NearlyMinimax.FieldPairMoments


@[expose] public section

/-! Primitive assumptions and their actual-law consequences for the paper's
independent pilots. The conditions contain no pair-risk conclusion. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

theorem regularPairDesignMeasure_ae_of_supported {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    {P : Covariate d × Covariate d → Prop}
    (hp : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → P w) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, P w := by
  change ∀ᵐ w ∂ENNReal.ofReal ((k : ℝ) ^ d) •
    ((designLaw θ).prod (designLaw θ)).restrict
      {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}, P w
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' (measurableSet_eq_fun
    ((regular_grid_cell_measurable k hk).comp measurable_fst)
    ((regular_grid_cell_measurable k hk).comp measurable_snd))).2
  filter_upwards [hp] with w hw hs
  apply hw
  have hs' : regularGridCell k hk w.1 = regularGridCell k hk w.2 := hs
  simp [sameLabelKernel, hs']

structure PairPilotAssumptions {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ) : Prop where
  constantNonnegative : 0 ≤ Cp
  budgetNonnegative : 0 ≤ W
  barMeasurable : Measurable bar
  noiseMeasurable : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2)
  barBound : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → ‖bar w‖ ≤ Cp
  noiseSection : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => η x w) 2 μ
  noiseEnergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
    sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ Cp * W
  noiseCentered : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0
  lamNonnegative : 0 ≤ lam
  linearTest : ∀ v : (Covariate d × Covariate d) → PairVector,
    MemLp v 2 (regularPairDesignMeasure θ k hk) →
    (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
      lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
include hp

theorem pairPilotCoefficient_measurable :
    Measurable (fun z : Ω × (Covariate d × Covariate d) => pairPilotCoefficient bar η z.1 z.2) :=
  (hp.barMeasurable.comp measurable_snd).add hp.noiseMeasurable

theorem pairPilotCoefficient_sections :
    ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        MemLp (fun x => pairPilotCoefficient bar η x w) 2 μ := by
  filter_upwards [hp.noiseSection] with w hw hs
  exact PilotFields.pilot_coefficient_memLp_two (bar w) (hw hs)

theorem pairPilotCoefficient_energy :
    ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        (∫ x, ‖pairPilotCoefficient bar η x w‖ ^ 2 ∂μ) ≤ 2 * Cp ^ 2 + 2 * Cp * W := by
  filter_upwards [hp.noiseSection, hp.barBound, hp.noiseEnergy] with w hs hb he hq
  simpa only [pairPilotCoefficient, mul_assoc] using
    PilotFields.pilot_coefficient_second_moment_le (bar w) (hs hq)
      hp.constantNonnegative (hb hq) (he hq)

include C hθ

theorem pairPilotScoreKernel_memLp :
    MemLp (fun z : (Ω × Ω) × (Observation d × Observation d) =>
      pairPilotScoreKernel θ k hk bar η z.1 z.2) 2
      ((μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) := by
  exact rawModelPairScore_memLp μ C θ hθ k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
      mul_nonneg hp.constantNonnegative hp.budgetNonnegative] : 0 ≤ 2 * Cp ^ 2 + 2 * Cp * W)
    (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)

theorem pairPilotNoiseKernel_memLp :
    MemLp (fun z : (Ω × Ω) × (Observation d × Observation d) =>
      pairPilotNoiseKernel k hk bar η z.1 z.2) 2
      ((μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) := by
  exact rawModelPairNoise_memLp μ C θ hθ k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
      mul_nonneg hp.constantNonnegative hp.budgetNonnegative] : 0 ≤ 2 * Cp ^ 2 + 2 * Cp * W)
    (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)

theorem pairPilotAssumptions_meanConditions :
    PairPilotMeanConditions θ k hk μ bar η Cp lam := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  let := observationLaw_isProbability C θ hθ
  have hs := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseSection
  have he := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseEnergy
  refine ⟨hp.barMeasurable, regularPairDesignMeasure_ae_of_supported θ k hk hp.barBound,
    hp.noiseMeasurable, ?_, hp.noiseCentered, hp.lamNonnegative, hp.linearTest, ?_, ?_⟩
  · exact PilotFields.memLp_joint_of_uniform_section_energy hp.noiseMeasurable hs
      (mul_nonneg hp.constantNonnegative hp.budgetNonnegative) he
  · exact ((pairPilotScoreKernel_memLp μ C θ hθ k hk bar η Cp W lam hp).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae
  · exact ((pairPilotNoiseKernel_memLp μ C θ hθ k hk bar η Cp W lam hp).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).prod_right_ae


theorem pairPilotScoreKernel_energy_le :
    (∫ z : (Ω × Ω) × (Observation d × Observation d),
      pairPilotScoreKernel θ k hk bar η z.1 z.2 ^ 2
      ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 *
        (responseOperatorEnergyBound C * (C.densityUpper / (k : ℝ) ^ d)) := by
  exact rawModelPairScore_energy_le μ C θ hθ k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
      mul_nonneg hp.constantNonnegative hp.budgetNonnegative])
    (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)

theorem pairPilotNoiseKernel_energy_le :
    (∫ z : (Ω × Ω) × (Observation d × Observation d),
      pairPilotNoiseKernel k hk bar η z.1 z.2 ^ 2
      ∂(μ.prod μ).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      (2 * Cp ^ 2 + 2 * Cp * W) ^ 2 * (4 * (C.densityUpper / (k : ℝ) ^ d)) := by
  exact rawModelPairNoise_energy_le μ C θ hθ k hk
    (pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp)
    (pairPilotCoefficient_sections μ θ k hk bar η Cp W lam hp)
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative,
      mul_nonneg hp.constantNonnegative hp.budgetNonnegative])
    (pairPilotCoefficient_energy μ θ k hk bar η Cp W lam hp)

end
end NearlyMinimax
