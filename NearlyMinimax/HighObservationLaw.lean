module

public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.LowMixtureLaw
public import Mathlib.Probability.Kernel.Composition.WithDensity


@[expose] public section

/-! Genuine normalized high-prior observation laws. Positivity of the raw
 density makes every raw state a probability experiment; the exceptional
 mass-concentration event is not needed for probability normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem highRawDensity_integrable_of_interval {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    Integrable p (cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  apply (integrable_const b).mono' hp.aestronglyMeasurable
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans hx.1)]
  exact hx.2

theorem highRawDensityMass_mem_Icc {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    highRawDensityMass p ∈ Icc a b := by
  let _ := cubeVolume_isProbability d
  have hi := highRawDensity_integrable_of_interval p hp a b ha hb
  constructor
  · simpa [highRawDensityMass] using
      integral_mono_ae (integrable_const a) hi (hb.mono fun x hx => hx.1)
  · simpa [highRawDensityMass] using
      integral_mono_ae hi (integrable_const b) (hb.mono fun x hx => hx.2)

theorem normalizedDensityTernaryParameter_design_probability {d : ℕ}
    (p : Covariate d → ℝ) (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    IsProbabilityMeasure ((cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x))) := by
  let _ := cubeVolume_isProbability d
  have hi := highRawDensity_integrable_of_interval p hp a b ha hb
  have hm := highRawDensityMass_mem_Icc p hp a b ha hb
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa using highNormalizedDensity_normalized p hi
    (hb.mono fun x hx => ha.le.trans hx.1) (ha.trans_le hm.1)

theorem normalizedDensityTernaryParameter_observation_index_map {d : ℕ}
    (p : Covariate d → ℝ) (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))))
    (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))).compProd (responseIndexKernel a V F hF)).map
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) =
      observationLaw (normalizedDensityTernaryParameter p F a V hF ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := hdesign
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := ternaryErrorKernel_markov a V F hF ha hp
  have hencode : Measurable (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) :=
    measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
  have hreal : Measurable (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  ext s hs
  rw [Measure.map_apply hencode hs, observationLaw]
  change _ = (((designLaw (normalizedDensityTernaryParameter p F a V hF ha hp)).compProd
    (ternaryErrorKernel a V F hF)).map (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2))) s
  rw [Measure.map_apply hreal hs]
  change _ = (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))).compProd (ternaryErrorKernel a V F hF)) ((fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) ⁻¹' s)
  rw [Measure.compProd_apply (hs.preimage hencode), Measure.compProd_apply (hs.preimage hreal)]
  apply lintegral_congr
  intro x
  have hSreal : MeasurableSet {u : ℝ | (x, F x + u) ∈ s} :=
    hs.preimage (measurable_const.prodMk (measurable_const.add measurable_id))
  have hSindex : MeasurableSet {y : Fin 3 | (x, ternaryValue a y) ∈ s} :=
    hs.preimage (measurable_const.prodMk (measurable_of_countable _))
  simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  change Measure.dirac y {y | (x, ternaryValue a y) ∈ s} =
    Measure.dirac (ternaryValue a y - F x) {u | (x, F x + u) ∈ s}
  rw [Measure.dirac_apply' _ hSindex, Measure.dirac_apply' _ hSreal]
  have he : F x + (ternaryValue a y - F x) = ternaryValue a y := by ring
  by_cases h : (x, ternaryValue a y) ∈ s <;> simp [Set.indicator, he, h]

theorem normalizedDensityTernaryParameter_sample_index_map {d : ℕ}
    (p : Covariate d → ℝ) (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))))
    (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => (cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x)))).compProd
      (responseSampleIndexKernel n a V F hF)).map (encodeDesignResponse a) =
      sampleLaw (normalizedDensityTernaryParameter p F a V hF ha hp) n := by
  let _ := cubeVolume_isProbability d
  let _ := hdesign
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hsingle : MeasurePreserving
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2))
      (((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))).compProd (responseIndexKernel a V F hF))
      (observationLaw (normalizedDensityTernaryParameter p F a V hF ha hp)) :=
    ⟨measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd),
      normalizedDensityTernaryParameter_observation_index_map p hdesign a V F hF ha hp⟩
  let _ : IsProbabilityMeasure (observationLaw (normalizedDensityTernaryParameter p F a V hF ha hp)) := by
    rw [← hsingle.map_eq]
    infer_instance
  have h := (measurePreserving_pi _ _ (fun _ : Fin n => hsingle)).map_eq
  rw [← responseSampleIndexKernel_joint_map ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))) n a V F hF ha hp,
    Measure.map_map] at h
  · exact h
  · apply Measurable.of_eval
    intro i
    exact (measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)).comp
      (measurable_pi_apply i)
  · fun_prop



theorem responseIndexKernel_eq_withDensity {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) :
    responseIndexKernel a V F hF =
      (Kernel.const α (Measure.count : Measure (Fin 3))).withDensity
        (fun x y => ENNReal.ofReal (ternaryMass a (F x) V y)) := by
  have hq : Measurable (fun z : α × Fin 3 =>
      ENNReal.ofReal (ternaryMass a (F z.1) V z.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    exact ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)
  ext x : 1
  rw [Kernel.withDensity_apply _ hq]
  simp only [Kernel.const_apply, count_withDensity, Measure.sum_fintype,
    responseIndexKernel_apply]

theorem responseSampleIndexKernel_eq_withDensity {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) :
    responseSampleIndexKernel n a V F hF =
      (Kernel.const (Fin n → α) (Measure.count : Measure (Fin n → Fin 3))).withDensity
        (fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) := by
  have hq : Measurable (fun z : (Fin n → α) × (Fin n → Fin 3) =>
      ENNReal.ofReal (∏ i, ternaryMass a (F (z.1 i)) V (z.2 i))) := by
    apply measurable_from_prod_countable_left
    intro y
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V (fun x : Fin n → α => F (x i))
        (hF.comp (measurable_pi_apply i)) (y i))
  ext x : 1
  rw [Kernel.withDensity_apply _ hq]
  simp only [Kernel.const_apply, count_withDensity, Measure.sum_fintype,
    responseSampleIndexKernel_apply]

/-- Density tensorization for a finite iid product, proved on measurable boxes. -/
theorem probability_pi_withDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    (hprob : IsProbabilityMeasure (μ.withDensity f)) (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ.withDensity f) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f (x i)) := by
  let _ := hprob
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator]
  · have he (x : Fin n → α) :
        (Set.pi Set.univ s).indicator (fun x => ∏ i, f (x i)) x =
          ∏ i, (s i).indicator f (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp [Set.indicator_of_mem, Set.mem_pi, h]
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hz : ∏ j, (s j).indicator f (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)
        rw [hz]
        apply Set.indicator_of_notMem
        simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
        exact not_forall.mpr ⟨i, hi⟩
    simp_rw [he]
    let G : Fin n → α → ℝ≥0∞ := fun i => (s i).indicator f
    have hG : ∀ i, Measurable (G i) := fun i => hf.indicator (hs i)
    change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi (fun _ : Fin n => μ)) = _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
      (iIndepFun_pi (fun i => (hG i).aemeasurable))
      (fun i => (hG i).comp (measurable_pi_apply i))]
    apply Finset.prod_congr rfl
    intro i _
    rw [(measurePreserving_eval (fun _ : Fin n => μ) i).lintegral_comp (hG i)]
    change (∫⁻ b, (s i).indicator f b ∂μ) = _
    rw [lintegral_indicator (hs i), withDensity_apply f (hs i)]
  · exact MeasurableSet.univ_pi hs

def highObservationLikelihood {d : ℕ} (a V : ℝ)
    (p F : Covariate d → ℝ) (z : Covariate d × Fin 3) : ℝ :=
  highNormalizedDensity p z.1 * ternaryMass a (F z.1) V z.2

def highSampleLikelihood {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∏ i, p (z.1 i)) / highRawDensityMass p ^ n *
    ∏ i, ternaryMass a (F (z.1 i)) V (z.2 i)

/-- Exact single-observation density before the real-response encoding. -/
theorem highObservation_index_density {d : ℕ} (p F : Covariate d → ℝ)
    (hp : Measurable p) (hF : Measurable F) (a V : ℝ) :
    ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))).compProd
      (responseIndexKernel a V F hF) =
    ((cubeVolume d).prod (Measure.count : Measure (Fin 3))).withDensity
      (fun z => ENNReal.ofReal (highNormalizedDensity p z.1) *
        ENNReal.ofReal (ternaryMass a (F z.1) V z.2)) := by
  let _ := cubeVolume_isProbability d
  have hq : Measurable (fun z : Covariate d × Fin 3 =>
      ENNReal.ofReal (ternaryMass a (F z.1) V z.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    exact ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun x y => ENNReal.ofReal (ternaryMass a (F x) V y))
    (Kernel.const (Covariate d) (Measure.count : Measure (Fin 3)))
    (fun _ _ => ENNReal.ofReal_ne_top)
  rw [responseIndexKernel_eq_withDensity,
    Measure.withDensity_compProd_withDensity
      (f := fun x => ENNReal.ofReal (highNormalizedDensity p x))
      (g := fun x y => ENNReal.ofReal (ternaryMass a (F x) V y))
      (ENNReal.measurable_ofReal.comp (highNormalizedDensity_measurable p hp)) hq,
    Measure.compProd_const]

/-- Exact iid sample density with the raw mass raised to the sample size. -/
theorem highSample_index_density {d : ℕ} (n : ℕ) (p F : Covariate d → ℝ)
    (hp : Measurable p) (hF : Measurable F) (a V : ℝ)
    (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x))))
    (hraw : ∀ x, 0 ≤ p x) (hm : 0 < highRawDensityMass p)
    (hq0 : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => (cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x)))).compProd
      (responseSampleIndexKernel n a V F hF)) =
    ((Measure.pi (fun _ : Fin n => cubeVolume d)).prod
      (Measure.count : Measure (Fin n → Fin 3))).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood n a V p F z)) := by
  let _ := cubeVolume_isProbability d
  have hf : Measurable (fun x => ENNReal.ofReal (highNormalizedDensity p x)) :=
    ENNReal.measurable_ofReal.comp (highNormalizedDensity_measurable p hp)
  have hq : Measurable (fun z : (Fin n → Covariate d) × (Fin n → Fin 3) =>
      ENNReal.ofReal (∏ i, ternaryMass a (F (z.1 i)) V (z.2 i))) := by
    apply measurable_from_prod_countable_left
    intro y
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V (fun x : Fin n → Covariate d => F (x i))
        (hF.comp (measurable_pi_apply i)) (y i))
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
    (Kernel.const (Fin n → Covariate d) (Measure.count : Measure (Fin n → Fin 3)))
    (fun _ _ => ENNReal.ofReal_ne_top)
  rw [probability_pi_withDensity (cubeVolume d) _ hf hdesign n,
    responseSampleIndexKernel_eq_withDensity,
    Measure.withDensity_compProd_withDensity
      (f := fun x : Fin n → Covariate d => ∏ i, ENNReal.ofReal (highNormalizedDensity p (x i)))
      (g := fun (x : Fin n → Covariate d) (y : Fin n → Fin 3) => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
      (Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))) hq,
    Measure.compProd_const]
  congr 1
  funext z
  have hpn (i : Fin n) : 0 ≤ highNormalizedDensity p (z.1 i) :=
    div_nonneg (hraw (z.1 i)) hm.le
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hpn i),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => hpn i))]
  congr 1
  simp [highSampleLikelihood, highNormalizedDensity, Finset.prod_div_distrib]

end NearlyMinimax
