module

public import NearlyMinimax.HighObservationKernel


@[expose] public section

/-! Original real-response kernel and likelihood integrals for the high prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The jointly Borel experiment on the original real observation space. -/
def highRealSampleKernel {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : Kernel Ω (Fin n → Observation d) :=
  (highSampleIndexKernel n a V p F hp hF).map (encodeDesignResponse a)

theorem highRealSampleKernel_apply {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      (highSampleIndexKernel n a V p F hp hF ω).map (encodeDesignResponse a) :=
  Kernel.map_apply _ (encodeDesignResponse_measurable a) ω

theorem highRealSampleKernel_markov {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    IsMarkovKernel (highRealSampleKernel n a V p F hp hF) := by
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  exact Kernel.IsMarkovKernel.map _ (encodeDesignResponse_measurable a)

/-- Each fiber is the actual original-model sample law. -/
theorem highRealSampleKernel_eq_sampleLaw {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      sampleLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hF.of_uncurry_left ha (hq ω)) n := by
  rw [highRealSampleKernel_apply]
  exact highSampleIndexKernel_encode n a V p F hp hF aRaw bRaw haRaw hraw ha hq ω

/-- Nonnegative likelihoods follow from the genuine raw/response constraints. -/
theorem highSampleLikelihood_nonneg {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (hp : ∀ x, 0 ≤ p x) (hm : 0 < highRawDensityMass p)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    0 ≤ highSampleLikelihood n a V p F z := by
  exact mul_nonneg (div_nonneg (Finset.prod_nonneg (fun i _ => hp (z.1 i)))
    (pow_nonneg hm.le n)) (Finset.prod_nonneg (fun i _ => hq (z.1 i) (z.2 i)))

/-- Exact reference-density integration; no finite-risk assumption is needed. -/
theorem highSampleIndexKernel_lintegral {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω)
    (G : ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ z, G z ∂highSampleIndexKernel n a V p F hp hF ω) =
      ∫⁻ z, ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z) * G z
        ∂highSampleReference d n := by
  rw [highSampleIndexKernel_apply]
  have hj : Measurable (Function.uncurry (fun ω z =>
      highSampleLikelihood n a V (p ω) (F ω) z)) :=
    highSampleLikelihood_joint_measurable n a V p F hp hF
  have hw : Measurable (fun z => highSampleLikelihood n a V (p ω) (F ω) z) :=
    hj.of_uncurry_left
  exact lintegral_withDensity_eq_lintegral_mul _
    (ENNReal.measurable_ofReal.comp hw) hG

theorem highRealSampleKernel_lintegral {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω)
    (G : (Fin n → Observation d) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ z, G z ∂highRealSampleKernel n a V p F hp hF ω) =
      ∫⁻ z, ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z) *
        G (encodeDesignResponse a z) ∂highSampleReference d n := by
  rw [highRealSampleKernel_apply, lintegral_map hG (encodeDesignResponse_measurable a)]
  exact highSampleIndexKernel_lintegral n a V p F hp hF ω _
    (hG.comp (encodeDesignResponse_measurable a))

/-- The original estimator risk is the normalized likelihood integral. -/
theorem normalizedDensityTernaryParameter_risk_likelihood {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω)
    (T : Estimator d n) :
    meanSquaredRisk T (normalizedDensityTernaryParameter (p ω) (F ω) a V
      hF.of_uncurry_left ha (hq ω)) =
      ∫⁻ z, ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z) *
        ENNReal.ofReal ((T.val (encodeDesignResponse a z) - V) ^ 2)
        ∂highSampleReference d n := by
  unfold meanSquaredRisk
  rw [← highRealSampleKernel_eq_sampleLaw n a V p F hp hF aRaw bRaw haRaw hraw ha hq ω]
  exact highRealSampleKernel_lintegral n a V p F hp hF ω _
    (ENNReal.measurable_ofReal.comp ((T.property.sub_const V).pow_const 2))

/-- Counting on response vectors is exactly the product of the three-point references. -/
theorem ternary_counting_pi (n : ℕ) :
    Measure.pi (fun _ : Fin n => (Measure.count : Measure (Fin 3))) =
      (Measure.count : Measure (Fin n → Fin 3)) := by
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.pi_singleton]
  simp

theorem highSampleReference_eq_product_counting (d n : ℕ) :
    highSampleReference d n =
      (Measure.pi (fun _ : Fin n => cubeVolume d)).prod
        (Measure.pi (fun _ : Fin n => (Measure.count : Measure (Fin 3)))) := by
  rw [ternary_counting_pi]
  rfl

/-- The displayed source likelihood, with the inverse mass to the power n. -/
theorem highSampleLikelihood_eq_inv_mass_product {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    highSampleLikelihood n a V p F z =
      (highRawDensityMass p)⁻¹ ^ n *
        ∏ i, p (z.1 i) * ternaryMass a (F (z.1 i)) V (z.2 i) := by
  simp only [highSampleLikelihood, Finset.prod_mul_distrib, div_eq_mul_inv, inv_pow]
  ring

theorem highSampleLikelihood_normalized {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω) :
    (∫⁻ z, ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)
      ∂highSampleReference d n) = 1 := by
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  have h := measure_univ (μ := highSampleIndexKernel n a V p F hp hF ω)
  rw [highSampleIndexKernel_apply, withDensity_apply _ MeasurableSet.univ] at h
  simpa using h

theorem highSampleIndexKernel_absolutelyContinuous {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highSampleIndexKernel n a V p F hp hF ω ≪ highSampleReference d n := by
  rw [highSampleIndexKernel_apply]
  exact withDensity_absolutelyContinuous _ _

end NearlyMinimax
