module

public import NearlyMinimax.AbsolutelyContinuousPathRisk
public import NearlyMinimax.Clipping


@[expose] public section

/-! Exceptional-state risk control for actual probability mixtures of original
sample laws. Clipping and the exceptional contribution are both derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem probability_kernel_integral {Α Ω : Type*} [MeasurableSpace Α] [MeasurableSpace Ω]
    (μ : Measure Α) [IsProbabilityMeasure μ] (K : Kernel Α Ω) [IsMarkovKernel K]
    (f : Ω → ℝ) (hf : Integrable f (K ∘ₘ μ)) :
    (∫ x, f x ∂(K ∘ₘ μ)) = ∫ a, ∫ x, f x ∂K a ∂μ := by
  have h := Kernel.integral_comp (κ := Kernel.const Unit μ) (η := K) (a := ())
    (f := f) (by simpa only [← Measure.comp_eq_comp_const_apply] using hf)
  simpa only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply] using h

theorem boundedEstimator_worstCaseRisk_finite {d n : ℕ} (C : ModelConstants d)
    (T : BoundedEstimator C n) : worstCaseRisk C T.val < ∞ := by
  have hb : worstCaseRisk C T.val ≤
      ENNReal.ofReal ((effectiveVarianceUpper C - C.varianceLower) ^ 2) :=
    iSup_le (fun θ => boundedEstimator_risk_le_diameter C T θ.val θ.property)
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem boundedEstimator_mixture_risk_le_of_exceptional_set {Α : Type*} [MeasurableSpace Α]
    {d n : ℕ} (C : ModelConstants d) (T : BoundedEstimator C n)
    (σ : Measure Α) [IsProbabilityMeasure σ]
    (L : Kernel Α (Fin n → Observation d)) [IsMarkovKernel L]
    (θ : Α → RegressionParameter d) (V ε : ℝ)
    (hL : ∀ a, L a = sampleLaw (θ a) n) (hVθ : ∀ a, (θ a).variance = V)
    (hV : V ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : Set Α) (hbad : MeasurableSet bad)
    (hlegal : ∀ a ∉ bad, Admissible C (θ a))
    (hmass : σ.real bad ≤ ε) :
    (∫ x, (T.val.val x - V) ^ 2 ∂(L ∘ₘ σ)) ≤
      (worstCaseRisk C T.val).toReal + (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε := by
  let D := effectiveVarianceUpper C - C.varianceLower
  let f (x : Fin n → Observation d) := (T.val.val x - V) ^ 2
  have hfmeas : Measurable f := by
    dsimp only [f]
    exact (T.val.property.sub_const V).pow_const (2 : ℕ)
  have hf0 (x : Fin n → Observation d) : 0 ≤ f x := sq_nonneg _
  have hcap (x : Fin n → Observation d) : f x ≤ D ^ 2 := by
    have ht := T.property x
    have hh : |T.val.val x - V| ≤ D := by
      apply abs_le.mpr
      constructor <;> dsimp only [D] <;> linarith only [ht.1, ht.2, hV.1, hV.2]
    have hD : 0 ≤ D := sub_nonneg.mpr (effective_variance_interval_nondegenerate C).le
    simpa only [f, sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr hh
  have hfi (μ : Measure (Fin n → Observation d)) [IsProbabilityMeasure μ] : Integrable f μ := by
    apply (integrable_const (D ^ 2)).mono' hfmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hcap x
  let e (a : Α) := ∫ x, f x ∂L a
  have hemeas : Measurable e := hfmeas.stronglyMeasurable.integral_kernel.measurable
  have he0 (a : Α) : 0 ≤ e a := integral_nonneg hf0
  have hecap (a : Α) : e a ≤ D ^ 2 := by
    have h := integral_mono (hfi (L a)) (integrable_const (D ^ 2)) hcap
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hei : Integrable e σ := by
    apply (integrable_const (D ^ 2)).mono' hemeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he0 a)]
      exact hecap a
  have hgood (a : Α) (ha : Admissible C (θ a)) : e a ≤ (worstCaseRisk C T.val).toReal := by
    have heq : ENNReal.ofReal (e a) = meanSquaredRisk T.val (θ a) := by
      rw [meanSquaredRisk, ← hL a, hVθ a]
      exact ofReal_integral_eq_lintegral_ofReal (hfi (L a))
        (Filter.Eventually.of_forall hf0)
    have h := ENNReal.toReal_mono (boundedEstimator_worstCaseRisk_finite C T).ne
      (meanSquaredRisk_le_worstCaseRisk C T.val (θ a) ha)
    rwa [← heq, ENNReal.toReal_ofReal (he0 a)] at h
  rw [probability_kernel_integral σ L f (hfi (L ∘ₘ σ))]
  exact probability_mixture_exceptional_risk_bound σ e bad hbad
    (worstCaseRisk C T.val).toReal D ε hei ENNReal.toReal_nonneg
    (Filter.Eventually.of_forall (fun a ha => hgood a (hlegal a ha)))
    (Filter.Eventually.of_forall (fun a _ => hecap a)) hmass

theorem boundedEstimator_mixture_risk_le {Α : Type*} [MeasurableSpace Α]
    {d n : ℕ} (C : ModelConstants d) (T : BoundedEstimator C n)
    (σ : Measure Α) [IsProbabilityMeasure σ]
    (L : Kernel Α (Fin n → Observation d)) [IsMarkovKernel L]
    (θ : Α → RegressionParameter d) (V ε : ℝ)
    (hL : ∀ a, L a = sampleLaw (θ a) n) (hVθ : ∀ a, (θ a).variance = V)
    (hV : V ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (hbad : MeasurableSet {a | ¬ Admissible C (θ a)})
    (hmass : σ.real {a | ¬ Admissible C (θ a)} ≤ ε) :
    (∫ x, (T.val.val x - V) ^ 2 ∂(L ∘ₘ σ)) ≤
      (worstCaseRisk C T.val).toReal + (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε :=
  boundedEstimator_mixture_risk_le_of_exceptional_set C T σ L θ V ε hL hVθ hV
    {a | ¬ Admissible C (θ a)} hbad (fun _ ha => not_not.mp ha) hmass

end NearlyMinimax
