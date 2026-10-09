module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.PairWindowModel


@[expose] public section

/-! Localized fourth-moment control of the actual response operators. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Partition
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableEq I]
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (label : E → I) (hlabel : Measurable label)
  (r : E → ℝ) (hmr : Measurable r)
include hlabel hmr

def localizedResponseOperatorEnergy (V : ℝ) (z : E × E) : ℝ :=
  sameLabelKernel label z * ‖pairScoreOperator V (r z.1) (r z.2)‖ ^ 2

theorem localizedResponseOperatorEnergy_measurable (V : ℝ) :
    Measurable (localizedResponseOperatorEnergy label r V) :=
  (sameLabelKernel_measurable label hlabel).mul
    ((((pairScoreOperator_continuous V).measurable.comp
      ((hmr.comp measurable_fst).prodMk (hmr.comp measurable_snd))).norm).pow_const 2)

theorem localizedResponseOperatorEnergy_integrable (V : ℝ)
    (hr4 : Integrable (fun x => r x ^ 4) μ) :
    Integrable (localizedResponseOperatorEnergy label r V) (μ.prod μ) := by
  let G := labelLocalizedKernel label (fun x => r x ^ 4)
  have hG : Integrable G (μ.prod μ) := labelLocalizedKernel_integrable μ label hlabel _ hr4
  have hGs : Integrable (fun z : E × E => G z.swap) (μ.prod μ) :=
    integrable_swap_iff.mpr hG
  have hq := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hi : Integrable (fun z : E × E =>
      6 * G z + 6 * G z.swap + (6 + 8 * V ^ 2) * sameLabelKernel label z) (μ.prod μ) :=
    ((hG.const_mul 6).add (hGs.const_mul 6)).add (hq.const_mul _)
  have hm : Measurable (localizedResponseOperatorEnergy label r V) := by
    apply (sameLabelKernel_measurable label hlabel).mul
    exact (((pairScoreOperator_continuous V).measurable.comp
      ((hmr.comp measurable_fst).prodMk (hmr.comp measurable_snd))).norm.pow_const 2)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by unfold sameLabelKernel; split_ifs <;> norm_num) (sq_nonneg _))]
  by_cases he : label z.1 = label z.2
  · have hb := pairScoreOperator_norm_sq_le V (r z.1) (r z.2)
    simpa only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
      labelLocalizedKernel, G, Prod.fst_swap, Prod.snd_swap, eq_comm, one_mul, mul_one] using
      (show ‖pairScoreOperator V (r z.1) (r z.2)‖ ^ 2 ≤
        6 * r z.2 ^ 4 + 6 * r z.1 ^ 4 + (6 + 8 * V ^ 2) by nlinarith [hb])
  · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, G,
      he, Ne.symm he]

theorem localizedResponseOperatorEnergy_integral_le (V B4 : ℝ)
    (hr4 : Integrable (fun x => r x ^ 4) μ)
    (hloc : ∀ i : I, (∫ x, (label ⁻¹' {i}).indicator (fun x => r x ^ 4) x ∂μ) ≤
      B4 * μ.real (label ⁻¹' {i})) :
    (∫ z, localizedResponseOperatorEnergy label r V z ∂μ.prod μ) ≤
      (12 * B4 + 6 + 8 * V ^ 2) * ∑ i : I, μ.real (label ⁻¹' {i}) ^ 2 := by
  let G := labelLocalizedKernel label (fun x => r x ^ 4)
  have hG : Integrable G (μ.prod μ) := labelLocalizedKernel_integrable μ label hlabel _ hr4
  have hGs : Integrable (fun z : E × E => G z.swap) (μ.prod μ) :=
    integrable_swap_iff.mpr hG
  have hq := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hupper := labelLocalizedKernel_integral_le μ label hlabel _ hr4 B4 hloc
  have hb : (∫ z, localizedResponseOperatorEnergy label r V z ∂μ.prod μ) ≤
      ∫ z : E × E, 6 * G z + 6 * G z.swap +
        (6 + 8 * V ^ 2) * sameLabelKernel label z ∂μ.prod μ := by
    apply integral_mono (localizedResponseOperatorEnergy_integrable μ label hlabel r hmr V hr4)
      (((hG.const_mul 6).add (hGs.const_mul 6)).add (hq.const_mul _))
    intro z
    simp only [Pi.add_apply, Pi.mul_apply]
    by_cases he : label z.1 = label z.2
    · have hb := pairScoreOperator_norm_sq_le V (r z.1) (r z.2)
      simp only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
        labelLocalizedKernel, G, Prod.fst_swap, Prod.snd_swap, eq_comm, one_mul]
      nlinarith [hb]
    · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, G,
        he, Ne.symm he]
  have ha := integral_add ((hG.const_mul 6).add (hGs.const_mul 6)) (hq.const_mul (6 + 8 * V ^ 2))
  have ha' := integral_add (hG.const_mul 6) (hGs.const_mul 6)
  simp only [Pi.add_apply, Pi.mul_apply] at ha ha'
  rw [ha, ha', integral_const_mul, integral_const_mul, integral_const_mul,
    integral_prod_swap G, sameLabelKernel_integral μ label hlabel] at hb
  change (∫ z, G z ∂μ.prod μ) ≤ _ at hupper
  nlinarith

end Partition

def responseOperatorEnergyBound {d : ℕ} (C : ModelConstants d) : ℝ :=
  12 * responseFourthBound C + 6 + 8 * C.varianceUpper ^ 2

theorem responseOperatorEnergyBound_pos {d : ℕ} (C : ModelConstants d) :
    0 < responseOperatorEnergyBound C := by
  have h4 := responseFourthBound_pos C
  unfold responseOperatorEnergyBound
  positivity

theorem regularResponseOperatorEnergy_integrable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    Integrable (localizedResponseOperatorEnergy (regularObservationLabel k hk)
      Prod.snd θ.variance) ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact localizedResponseOperatorEnergy_integrable (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
      (observationLaw_response_fourth_integrable C θ hθ)

theorem regularResponseOperatorEnergy_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z, localizedResponseOperatorEnergy (regularObservationLabel k hk)
      Prod.snd θ.variance z ∂(observationLaw θ).prod (observationLaw θ)) ≤
      responseOperatorEnergyBound C * (C.densityUpper / (k : ℝ) ^ d) := by
  let := observationLaw_isProbability C θ hθ
  have hb := localizedResponseOperatorEnergy_integral_le (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
    (responseFourthBound C) (observationLaw_response_fourth_integrable C θ hθ) (by
      intro i
      rw [regularObservationLabel_mass C θ hθ k hk i, regularObservationLabel_fiber k hk i]
      exact observationLaw_localized_fourth_integral_le C θ hθ _
        ((measurableSet_singleton i).preimage (regular_grid_cell_measurable k hk)))
  simp_rw [regularObservationLabel_mass C θ hθ k hk] at hb
  have hV0 : 0 ≤ θ.variance := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVup := hθ.2.2.2.2.2.2.1
  have hvsq : θ.variance ^ 2 ≤ C.varianceUpper ^ 2 := pow_le_pow_left₀ hV0 hVup 2
  have hmass : 0 ≤ regularGridCollisionMass θ k hk := by
    unfold regularGridCollisionMass
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change _ ≤ (12 * responseFourthBound C + 6 + 8 * θ.variance ^ 2) *
    regularGridCollisionMass θ k hk at hb
  apply hb.trans
  calc
    _ ≤ responseOperatorEnergyBound C * regularGridCollisionMass θ k hk := by
      apply mul_le_mul_of_nonneg_right _ hmass
      unfold responseOperatorEnergyBound
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk)
      (responseOperatorEnergyBound_pos C).le

end NearlyMinimax
