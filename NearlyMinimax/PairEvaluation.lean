module

public import NearlyMinimax.PilotMasking
public import NearlyMinimax.TwoStagePairRisk
public import NearlyMinimax.ResponseOperatorEnergy


@[expose] public section

/-! Genuine L² and second-moment bounds for the original model's random
pair-score kernel, using independent pilot second moments only. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

def pairCovariates {d : ℕ} (z : Observation d × Observation d) : Covariate d × Covariate d :=
  (z.1.1, z.2.1)

theorem pairCovariates_measurable (d : ℕ) : Measurable (pairCovariates (d := d)) :=
  measurable_fst.fst.prodMk measurable_snd.fst

theorem observationPair_covariates_measurePreserving {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MeasurePreserving pairCovariates ((observationLaw θ).prod (observationLaw θ))
      ((designLaw θ).prod (designLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact (observationLaw_fst_measurePreserving C θ hθ).prod
    (observationLaw_fst_measurePreserving C θ hθ)

def rawModelPairScore {Ω : Type*} {d : ℕ} (θ : RegressionParameter d)
    (k : ℕ) (hk : 0 < k) (c : Ω → Covariate d × Covariate d → PairVector)
    (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), pairScoreOperator θ.variance z.1.2 z.2.2
      (c p.2 (pairCovariates z))⟫

theorem observationPairScoreOperator_measurable_apply {d : ℕ} (V : ℝ) :
    Measurable (fun z : (Observation d × Observation d) × PairVector =>
      pairScoreOperator V z.1.1.2 z.1.2.2 z.2) := by
  have hv : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      pairResponseVector z.1.1.2 z.1.2.2) :=
    pairResponseVector_continuous.comp
      (continuous_fst.fst.snd.prodMk continuous_fst.snd.snd)
  have hi : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      ⟪pairResponseVector z.1.1.2 z.1.2.2, z.2⟫) := hv.inner continuous_snd
  have hs : Continuous (fun z : (Observation d × Observation d) × PairVector =>
      ⟪pairResponseVector z.1.1.2 z.1.2.2, z.2⟫ • pairResponseVector z.1.1.2 z.1.2.2) := hi.smul hv
  simpa only [pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, starRingEnd_apply, star_trivial,
    Pi.sub_def, Pi.smul_def, Function.comp_def] using
    (hs.sub ((pairNoiseOperator.continuous.comp continuous_snd).const_smul V)).measurable

theorem pilotOnObservations_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : Ω × (Observation d × Observation d) => c z.1 (pairCovariates z.2)) :=
  hmc.comp (measurable_fst.prodMk ((pairCovariates_measurable d).comp measurable_snd))

theorem rawModelPairScore_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairScore θ k hk c z.1 z.2) := by
  exact PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator θ.variance z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))

theorem rawModelPairScore_memLp {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    MemLp (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairScore θ k hk c z.1 z.2)
      2 ((π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator θ.variance z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
  · intro z
    unfold sameLabelKernel
    split_ifs <;> norm_num
  · exact regularResponseOperatorEnergy_integrable C θ hθ k hk
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE

theorem rawModelPairScore_energy_le {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    (∫ z : (Ω × Ω) × (Observation d × Observation d), rawModelPairScore θ k hk c z.1 z.2 ^ 2
      ∂(π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      L ^ 2 * (responseOperatorEnergyBound C * (C.densityUpper / (k : ℝ) ^ d)) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator θ.variance z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) θ.variance)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
    (fun z => by unfold sameLabelKernel; split_ifs <;> norm_num)
    (regularResponseOperatorEnergy_integrable C θ hθ k hk)
    (hmp.quasiMeasurePreserving.ae hc) hL (hmp.quasiMeasurePreserving.ae hE)
  exact he.trans (mul_le_mul_of_nonneg_left (regularResponseOperatorEnergy_le C θ hθ k hk)
    (sq_nonneg L))

end NearlyMinimax
