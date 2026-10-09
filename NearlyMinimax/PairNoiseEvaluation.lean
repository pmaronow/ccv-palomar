module

public import NearlyMinimax.PairEvaluation


@[expose] public section

/-! The same actual-law pilot-energy argument for the pair denominator. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem observationPairNoiseOperator_energy_integrable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    Integrable (fun z : Observation d × Observation d =>
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2)
      ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact ((sameLabelKernel_memLp (observationLaw θ) _
    (regularObservationLabel_measurable k hk)).integrable (by norm_num)).mul_const _

theorem observationPairNoiseOperator_energy_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z : Observation d × Observation d,
      sameLabelKernel (regularObservationLabel k hk) z * ‖pairNoiseOperator‖ ^ 2
      ∂(observationLaw θ).prod (observationLaw θ)) ≤ 4 * (C.densityUpper / (k : ℝ) ^ d) := by
  let := observationLaw_isProbability C θ hθ
  rw [integral_mul_const, sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable k hk)]
  simp_rw [regularObservationLabel_mass C θ hθ k hk]
  change regularGridCollisionMass θ k hk * ‖pairNoiseOperator‖ ^ 2 ≤ _
  have hq : 0 ≤ regularGridCollisionMass θ k hk := by
    unfold regularGridCollisionMass
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : ‖pairNoiseOperator‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) pairNoiseOperator_norm_le 2
    norm_num at h
    exact h
  calc
    _ ≤ regularGridCollisionMass θ k hk * 4 := mul_le_mul_of_nonneg_left hN hq
    _ ≤ _ := by have h := regularGridCollisionMass_upper C θ hθ k hk; linarith

def rawModelPairNoise {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Ω → Covariate d × Covariate d → PairVector)
    (p : Ω × Ω) (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), pairNoiseOperator (c p.2 (pairCovariates z))⟫

theorem rawModelPairNoise_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (k : ℕ) (hk : 0 < k) {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairNoise k hk c z.1 z.2) := by
  exact PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ : Observation d × Observation d => pairNoiseOperator)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))

theorem rawModelPairNoise_memLp {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    MemLp (fun z : (Ω × Ω) × (Observation d × Observation d) => rawModelPairNoise k hk c z.1 z.2)
      2 ((π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ : Observation d × Observation d => pairNoiseOperator)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
  · intro z
    unfold sameLabelKernel
    split_ifs <;> norm_num
  · exact observationPairNoiseOperator_energy_integrable C θ hθ k hk
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE

theorem rawModelPairNoise_energy_le {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2))
    (hc : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → MemLp (fun x => c x w) 2 π)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂π) ≤ L) :
    (∫ z : (Ω × Ω) × (Observation d × Observation d), rawModelPairNoise k hk c z.1 z.2 ^ 2
      ∂(π.prod π).prod ((observationLaw θ).prod (observationLaw θ))) ≤
      L ^ 2 * (4 * (C.densityUpper / (k : ℝ) ^ d)) := by
  let := observationLaw_isProbability C θ hθ
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections
    (μ := π) (ν := (observationLaw θ).prod (observationLaw θ))
    (c := fun x z => c x (pairCovariates z))
    (A := fun _ : Observation d × Observation d => pairNoiseOperator)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
    (fun z => by unfold sameLabelKernel; split_ifs <;> norm_num)
    (observationPairNoiseOperator_energy_integrable C θ hθ k hk)
    (hmp.quasiMeasurePreserving.ae hc) hL (hmp.quasiMeasurePreserving.ae hE)
  exact he.trans (mul_le_mul_of_nonneg_left (observationPairNoiseOperator_energy_le C θ hθ k hk)
    (sq_nonneg L))

end NearlyMinimax
