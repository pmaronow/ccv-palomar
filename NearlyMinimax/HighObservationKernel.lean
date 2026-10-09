module

public import NearlyMinimax.HighObservationLaw


@[expose] public section

/-! Jointly measurable, normalized high-prior experiments over arbitrary raw states. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]

theorem highRawDensityMass_joint_measurable {d : ℕ} (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (fun ω => highRawDensityMass (p ω)) := by
  let _ := cubeVolume_isProbability d
  exact hp.stronglyMeasurable.integral_prod_right.measurable

theorem highNormalizedDensity_joint_measurable {d : ℕ} (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (fun z : Ω × Covariate d => highNormalizedDensity (p z.1) z.2) := by
  exact hp.div ((highRawDensityMass_joint_measurable p hp).comp measurable_fst)

theorem ternaryMass_joint_measurable {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) :
    Measurable (fun z : α × Fin 3 => ternaryMass a (F z.1) V z.2) := by
  exact measurable_from_prod_countable_left fun y =>
    ternaryMass_measurable_comp a V F hF y

theorem highObservationLikelihood_joint_measurable {d : ℕ} (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × (Covariate d × Fin 3) =>
      highObservationLikelihood a V (p z.1) (F z.1) z.2) := by
  have hx : Measurable (fun z : Ω × (Covariate d × Fin 3) => (z.1, z.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  exact ((highNormalizedDensity_joint_measurable p hp).comp hx).mul
    ((ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp
      (hx.prodMk (measurable_snd.comp measurable_snd)))

theorem highSampleLikelihood_joint_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highSampleLikelihood n a V (p z.1) (F z.1) z.2) := by
  have hx (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact ((Finset.measurable_prod _ (fun i _ => hp.comp (hx i))).div
    (((highRawDensityMass_joint_measurable p hp).comp measurable_fst).pow_const n)).mul
    (Finset.measurable_prod _ (fun i _ =>
      (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp
        ((hx i).prodMk (hy i))))

/-- The actual normalized design family is a kernel without a mass-event restriction. -/
def highDesignKernel {d : ℕ} (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) : Kernel Ω (Covariate d) where
  toFun ω := (cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity (p ω) x))
  measurable' := by
    let _ := cubeVolume_isProbability d
    exact measurable_withDensity
      (ENNReal.measurable_ofReal.comp (highNormalizedDensity_joint_measurable p hp))

theorem highDesignKernel_apply {d : ℕ} (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (ω : Ω) :
    highDesignKernel p hp ω = (cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity (p ω) x)) := rfl

theorem highDesignKernel_markov {d : ℕ} (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ ω x, a ≤ p ω x ∧ p ω x ≤ b) : IsMarkovKernel (highDesignKernel p hp) := by
  constructor
  intro ω
  exact normalizedDensityTernaryParameter_design_probability (p ω)
    (hp.of_uncurry_left) a b ha
    (Filter.Eventually.of_forall (hb ω))

/-- Fixed reference measure for the full design/finite-response experiment. -/
def highSampleReference (d n : ℕ) : Measure ((Fin n → Covariate d) × (Fin n → Fin 3)) :=
  (Measure.pi (fun _ : Fin n => cubeVolume d)).prod Measure.count

instance highSampleReference_isFinite (d n : ℕ) : IsFiniteMeasure (highSampleReference d n) := by
  let _ := cubeVolume_isProbability d
  unfold highSampleReference
  infer_instance

/-- The joint sample kernel carries exactly the normalized raw likelihood. -/
def highSampleIndexKernel {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Kernel Ω ((Fin n → Covariate d) × (Fin n → Fin 3)) := by
  let _ := cubeVolume_isProbability d
  exact (Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))

theorem highSampleIndexKernel_apply {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highSampleIndexKernel n a V p F hp hF ω =
      (highSampleReference d n).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) := by
  let _ := cubeVolume_isProbability d
  have hl : Measurable (Function.uncurry (fun ω z =>
      ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)
  change ((Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) ω = _
  exact Kernel.withDensity_apply _ hl ω

/-- This family is a probability kernel on every raw state, including states
outside the original-model density interval after normalization. -/
theorem highSampleIndexKernel_markov {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    IsMarkovKernel (highSampleIndexKernel n a V p F hp hF) := by
  constructor
  intro ω
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  let hd := normalizedDensityTernaryParameter_design_probability (p ω) hpω aRaw bRaw haRaw
    (Filter.Eventually.of_forall (hraw ω))
  let _ := hd
  let _ := responseSampleIndexKernel_markov n a V (F ω) hFω ha (hq ω)
  have hm : 0 < highRawDensityMass (p ω) := haRaw.trans_le
    (highRawDensityMass_mem_Icc (p ω) hpω aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  rw [highSampleIndexKernel_apply, highSampleReference]
  rw [← highSample_index_density n (p ω) (F ω) hpω hFω a V hd
    (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  infer_instance

/-- Exact transfer of the normalized experiment to the original real-valued sample law. -/
theorem highSampleIndexKernel_encode {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω) :
    (highSampleIndexKernel n a V p F hp hF ω).map (encodeDesignResponse a) =
      sampleLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V
        hF.of_uncurry_left ha (hq ω)) n := by
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  have hd := normalizedDensityTernaryParameter_design_probability (p ω) hpω aRaw bRaw haRaw
    (Filter.Eventually.of_forall (hraw ω))
  have hm : 0 < highRawDensityMass (p ω) := haRaw.trans_le
    (highRawDensityMass_mem_Icc (p ω) hpω aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  rw [highSampleIndexKernel_apply, highSampleReference]
  rw [← highSample_index_density n (p ω) (F ω) hpω hFω a V hd
    (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  exact normalizedDensityTernaryParameter_sample_index_map (p ω) hd n a V (F ω) hFω ha (hq ω)

end NearlyMinimax
