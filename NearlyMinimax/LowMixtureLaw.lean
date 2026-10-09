module

public import NearlyMinimax.LowSmoothnessConstants
public import NearlyMinimax.ParametricLower


@[expose] public section

/-! # Actual probability laws of the low-smoothness mixture

The finite response labels encode the original real response experiment.
This file proves the law identification and transfers its risks to the
original model; it introduces no statistical risk premise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace NearlyMinimax

def responseIndexKernel {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel α (Fin 3) where
  toFun x := ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun y _ =>
      (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul_const _)

theorem responseIndexKernel_apply {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) (x : α) :
    responseIndexKernel a V F hF x =
      ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y := rfl

theorem responseIndexKernel_markov {α : Type*} [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseIndexKernel a V F hF) := by
  constructor
  intro x
  constructor
  simp only [responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp x y), ternary_normalized a (F x) V ha]
  simp

/-- Encoding the genuine conditional index law gives the original real-response
observation law, including its covariate-dependent error kernel. -/
theorem uniformTernaryParameter_observation_index_map {d : ℕ}
    (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((cubeVolume d).compProd (responseIndexKernel a V F hF)).map
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) =
      observationLaw (uniformTernaryParameter a V F hF ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := ternaryErrorKernel_markov a V F hF ha hp
  have hencode : Measurable (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) :=
    measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
  have hreal : Measurable (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  ext s hs
  rw [Measure.map_apply hencode hs, observationLaw]
  change _ = (((designLaw (uniformTernaryParameter a V F hF ha hp)).compProd
    (ternaryErrorKernel a V F hF)).map (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2))) s
  rw [Measure.map_apply hreal hs]
  simp only [designLaw, uniformTernaryParameter, ENNReal.ofReal_one, withDensity_const, one_smul]
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

/-- The genuine conditional law of all finite response labels. -/
def responseSampleIndexKernel {α : Type*} [MeasurableSpace α] (n : ℕ) (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel (Fin n → α) (Fin n → Fin 3) where
  toFun x := ∑ y : Fin n → Fin 3,
    ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro y _
    apply Measurable.mul_const
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V (fun x : Fin n → α => F (x i))
        (hF.comp (measurable_pi_apply i)) (y i))

theorem responseSampleIndexKernel_apply {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α) :
    responseSampleIndexKernel n a V F hF x =
      ∑ y : Fin n → Fin 3,
        ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y := rfl

theorem responseSampleIndexKernel_markov {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseSampleIndexKernel n a V F hF) := by
  constructor
  intro x
  constructor
  simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => Finset.prod_nonneg
      (fun i _ => hp (x i) (y i))), ← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

theorem responseSampleIndexKernel_lintegral {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α)
    (H : (Fin n → Fin 3) → ℝ≥0∞) :
    (∫⁻ y, H y ∂responseSampleIndexKernel n a V F hF x) =
      ∑ y, ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) * H y := by
  simp [responseSampleIndexKernel_apply, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]

/-- The sample kernel, with designs drawn independently, is the same law as
independent pairs from the one-observation kernel. -/
theorem responseSampleIndexKernel_joint_map {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => μ)).compProd
      (responseSampleIndexKernel n a V F hF)).map
      (fun z : (Fin n → α) × (Fin n → Fin 3) => fun i => (z.1 i, z.2 i)) =
      Measure.pi (fun _ : Fin n => μ.compProd (responseIndexKernel a V F hF)) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hm : Measurable (fun z : (Fin n → α) × (Fin n → Fin 3) =>
      fun i => (z.1 i, z.2 i)) := by fun_prop
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage hm)]
  have hinner (x : Fin n → α) :
      responseSampleIndexKernel n a V F hF x
        (Prod.mk x ⁻¹' (fun z : (Fin n → α) × (Fin n → Fin 3) =>
          fun i => (z.1 i, z.2 i)) ⁻¹' Set.pi Set.univ s) =
        ∏ i, ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F (x i)) V y) *
          (s i).indicator 1 (x i, y) := by
    simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hp (x i) _)]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Measure.dirac_apply' _ (((MeasurableSet.univ_pi hs).preimage hm).preimage measurable_prodMk_left)]
    by_cases h : ∀ i, (x i, y i) ∈ s i
    · have hprod : ∏ i, (s i).indicator (1 : α × Fin 3 → ℝ≥0∞) (x i, y i) = 1 := by
        simp [Set.indicator_of_mem, h]
      simp [Set.indicator_of_mem, h, Set.mem_pi]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hz : (s i).indicator (1 : α × Fin 3 → ℝ≥0∞) (x i, y i) = 0 :=
        Set.indicator_of_notMem hi _
      rw [Finset.prod_mul_distrib]
      have hzero : ∏ j, (s j).indicator (1 : α × Fin 3 → ℝ≥0∞) (x j, y j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hz
      rw [hzero, mul_zero]
      simp [Set.indicator_of_notMem, Set.mem_pi, h]
  simp_rw [hinner]
  let G : Fin n → α → ℝ≥0∞ := fun i x =>
    ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) * (s i).indicator 1 (x, y)
  have hG : ∀ i, Measurable (G i) := by
    intro i
    exact Finset.measurable_sum _ (fun y _ =>
      (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul
        ((Measurable.indicator measurable_const (hs i)).comp (measurable_id.prodMk measurable_const)))
  change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi (fun _ : Fin n => μ)) = _
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
    (iIndepFun_pi (fun i => (hG i).aemeasurable))
    (fun i => (hG i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [(measurePreserving_eval (fun _ : Fin n => μ) i).lintegral_comp (hG i)]
  rw [Measure.compProd_apply (hs i)]
  apply lintegral_congr
  intro x
  simp only [G, responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ ((hs i).preimage measurable_prodMk_left), smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  rfl

/-- Encode all finite response labels as the paper's real observations. -/
def encodeDesignResponse {d n : ℕ} (a : ℝ) :
    (Fin n → Covariate d) × (Fin n → Fin 3) → (Fin n → Observation d) :=
  fun z i => (z.1 i, ternaryValue a (z.2 i))

theorem encodeDesignResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (encodeDesignResponse (d := d) (n := n) a) := by
  exact (encodeResponse_measurable a).comp measurable_swap

/-- Identification with the complete iid sample law of the original model. -/
theorem uniformTernaryParameter_sample_index_map {d : ℕ}
    (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => cubeVolume d)).compProd
      (responseSampleIndexKernel n a V F hF)).map (encodeDesignResponse a) =
      sampleLaw (uniformTernaryParameter a V F hF ha hp) n := by
  let _ := cubeVolume_isProbability d
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hsingle : MeasurePreserving
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2))
      ((cubeVolume d).compProd (responseIndexKernel a V F hF))
      (observationLaw (uniformTernaryParameter a V F hF ha hp)) :=
    ⟨measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd),
      uniformTernaryParameter_observation_index_map a V F hF ha hp⟩
  let _ : IsProbabilityMeasure (observationLaw (uniformTernaryParameter a V F hF ha hp)) := by
    rw [← hsingle.map_eq]
    infer_instance
  have h := (measurePreserving_pi _ _ (fun _ : Fin n => hsingle)).map_eq
  rw [← responseSampleIndexKernel_joint_map (cubeVolume d) n a V F hF ha hp,
    Measure.map_map] at h
  · exact h
  · apply Measurable.of_eval
    intro i
    exact (measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)).comp
      (measurable_pi_apply i)
  · fun_prop

/-- Genuine finite conditional integrals, with no density representation
assumption, equal the likelihood sums used by the score proof. -/
theorem responseSampleIndexKernel_integral {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α)
    (hp : ∀ i y, 0 ≤ ternaryMass a (F (x i)) V y)
    (H : (Fin n → Fin 3) → ℝ) :
    (∫ y, H y ∂responseSampleIndexKernel n a V F hF x) =
      ∑ y, (∏ i, ternaryMass a (F (x i)) V (y i)) * H y := by
  rw [responseSampleIndexKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => hp i (y i)))]
  · intro y _
    let _ := (Measure.dirac y).smul_finite
      (c := ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) ENNReal.ofReal_ne_top
    exact Integrable.of_finite

/-- Bounded data-observable expectations in the genuine original sample law
are exactly the design-integrated finite likelihood expectations. -/
theorem uniformTernaryParameter_sample_integral {d : ℕ}
    (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : ∀ z, |H z| ≤ B) :
    (∫ z, H z ∂sampleLaw (uniformTernaryParameter a V F hF ha hp) n) =
      ∫ x, ∑ y : Fin n → Fin 3,
        (∏ i, ternaryMass a (F (x i)) V (y i)) * H (encodeDesignResponse a (x, y))
        ∂Measure.pi (fun _ : Fin n => cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hm := encodeDesignResponse_measurable (d := d) (n := n) a
  rw [← uniformTernaryParameter_sample_index_map n a V F hF ha hp,
    integral_map hm.aemeasurable hH.aestronglyMeasurable]
  have hi : Integrable (fun z => H (encodeDesignResponse a z))
      ((Measure.pi (fun _ : Fin n => cubeVolume d)).compProd
        (responseSampleIndexKernel n a V F hF)) :=
    (integrable_const B).mono' (hH.comp hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB _))
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    responseSampleIndexKernel_integral n a V F hF x (fun i y => hp (x i) y) _)

/-- Exact identification of the finite likelihood risk with the original
model's ENNReal mean-squared risk for every bounded measurable estimator. -/
theorem uniformTernaryParameter_risk_formula {d n : ℕ}
    (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (T : Estimator d n) (B : ℝ) (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y : Fin n → Fin 3,
      (∏ i, ternaryMass a (F (x i)) V (y i)) *
        (T.val (encodeDesignResponse a (x, y)) - V) ^ 2
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) =
      meanSquaredRisk T (uniformTernaryParameter a V F hF ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  let _ : IsProbabilityMeasure (sampleLaw (uniformTernaryParameter a V F hF ha hp) n) := by
    rw [← uniformTernaryParameter_sample_index_map n a V F hF ha hp]
    infer_instance
  have hm : Measurable (fun z => (T.val z - V) ^ 2) := (T.property.sub_const V).pow_const 2
  have hbound (z : Fin n → Observation d) : |(T.val z - V) ^ 2| ≤ (B + |V|) ^ 2 := by
    have he := (abs_sub (T.val z) V).trans (add_le_add (hB z) (le_refl |V|))
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he 2
  have hint : Integrable (fun z => (T.val z - V) ^ 2)
      (sampleLaw (uniformTernaryParameter a V F hF ha hp) n) :=
    (integrable_const ((B + |V|) ^ 2)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound z))
  rw [← uniformTernaryParameter_sample_integral n a V F hF ha hp _ hm _ hbound]
  exact ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))

/-- Every latent state risk is bounded by the genuine original-model
worst-case risk once its model legality has been proved. -/
theorem uniformTernaryParameter_finite_risk_le_worstCase {d n : ℕ}
    (C : ModelConstants d) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (hlegal : Admissible C (uniformTernaryParameter a V F hF ha hp))
    (T : Estimator d n) (B : ℝ) (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y : Fin n → Fin 3,
      (∏ i, ternaryMass a (F (x i)) V (y i)) *
        (T.val (encodeDesignResponse a (x, y)) - V) ^ 2
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤ worstCaseRisk C T := by
  rw [uniformTernaryParameter_risk_formula a V F hF ha hp T B hB]
  exact le_iSup (fun θ : {θ // Admissible C θ} => meanSquaredRisk T θ.val)
    ⟨_, hlegal⟩

/-- Exact risk formula for every concrete grid-prior state. -/
theorem gridPathParameter_risk_formula {d n : ℕ}
    (C : ModelConstants d) (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) (η t : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : Estimator d n) (B : ℝ) (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
        (fun ξ i => indexedGridField d k η ξ (x i)) ξ y *
        (T.val (encodeDesignResponse P.a (x, y)) - (P.v - η ^ 2 * t)) ^ 2
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) =
      meanSquaredRisk T (gridPathParameter C P k η t ξ hη ht hfield hvariance) := by
  have hf (x : Covariate d) : |indexedGridField d k η ξ x| ≤ P.ρ :=
    (indexedGridField_abs_bound d k η hη ξ x).trans (by nlinarith)
  have hp (x : Covariate d) (y : Fin 3) :
      0 ≤ ternaryMass P.a (indexedGridField d k η ξ x) (P.v - η ^ 2 * t) y :=
    P.c_pos.le.trans ((P.path_legality η t _ ht hvariance (hf x)).2.2.1 y)
  simpa only [gridPathParameter, LowSmoothnessTernaryConstants.pathParameter,
    LowSmoothnessTernaryConstants.variancePath, finiteResponseLikelihood] using
    uniformTernaryParameter_risk_formula P.a (P.v - η ^ 2 * t)
      (indexedGridField d k η ξ) (indexedGridField_continuous d k η ξ).measurable
      P.a_pos.ne' hp T B hB

/-- The prior risk contribution of every latent state is controlled by the
original bounded estimator's worst-case risk. -/
theorem gridPathParameter_finite_risk_le_worstCase {d n : ℕ}
    (C : ModelConstants d) (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) (η b t : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound)
    (T : BoundedEstimator C n) :
    ENNReal.ofReal (∫ x, ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
        (fun ξ i => indexedGridField d k η ξ (x i)) ξ y *
        (T.val.val (encodeDesignResponse P.a (x, y)) - (P.v - η ^ 2 * t)) ^ 2
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤ worstCaseRisk C T.val := by
  have hB (z : Fin n → Observation d) : |T.val.val z| ≤ effectiveVarianceUpper C := by
    rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
    exact (T.property z).2
  rw [gridPathParameter_risk_formula C P k η t ξ hη ht hfield hvariance T.val _ hB]
  exact le_iSup (fun θ : {θ // Admissible C θ} => meanSquaredRisk T.val θ.val)
    ⟨_, gridPathParameter_admissible C P k η b t ξ hk hs1 hb hη ht hfield
      hvariance hscale hholder⟩

/-- Clipped estimators have finite genuine worst-case risk, independently of
which admissible parameter realizes that risk. -/
theorem boundedEstimator_worstCaseRisk_ne_top {d n : ℕ} (C : ModelConstants d)
    (T : BoundedEstimator C n) : worstCaseRisk C T.val ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply iSup_le
  intro θ
  exact boundedEstimator_risk_le_diameter C T θ.val θ.property

end NearlyMinimax
