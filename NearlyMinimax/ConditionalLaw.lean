module

public import NearlyMinimax.Model


@[expose] public section

/-! Actual finite-product conditional sampling laws for the original model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace NearlyMinimax

/-- The indexed product of Markov kernels, evaluated coordinate by coordinate. -/
def finiteProductKernel {ι α β : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    Kernel (ι → α) (ι → β) where
  toFun x := Measure.pi (fun i => κ i (x i))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    induction s, hs using MeasurableSpace.induction_on_inter
        generateFrom_pi.symm isPiSystem_pi with
    | empty => simp only [measure_empty]; exact measurable_const
    | basic s hs =>
        obtain ⟨t, ht, rfl⟩ := hs
        simp_rw [Measure.pi_pi]
        exact Finset.measurable_prod Finset.univ
          (fun i _ => (Kernel.measurable_coe (κ i) (ht i (mem_univ i))).comp
            (measurable_pi_apply i))
    | compl s hs ih =>
        simp_rw [measure_compl hs (measure_ne_top _ _), measure_univ]
        exact measurable_const.sub ih
    | iUnion f hd hf ih =>
        simp_rw [measure_iUnion hd hf]
        exact Measurable.tsum ih
    | x_4 => infer_instance

instance finiteProductKernel_markov {ι α β : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (finiteProductKernel κ) :=
  ⟨fun x => inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun i => κ i (x i))))⟩

theorem finiteProductKernel_apply {ι α β : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] (x : ι → α) :
    finiteProductKernel κ x = Measure.pi (fun i => κ i (x i)) := rfl

/-- Reassemble separate design and error vectors into coordinate pairs. -/
def pairVectors {ι α β : Type*} (z : (ι → α) × (ι → β)) : ι → α × β :=
  fun i => (z.1 i, z.2 i)

theorem pairVectors_measurable {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (pairVectors (ι := ι) (α := α) (β := β)) :=
  Measurable.of_eval (fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

/-- Tonelli factorization for coordinate functions under a product probability law. -/
theorem lintegral_coordinate_product {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ a, f i a ∂μ i := by
  have h := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun (i : ι) (x : ι → α) => f i (x i))
    (iIndepFun_pi (μ := μ) (X := f) (fun i => (hf i).aemeasurable))
    (fun i => (hf i).comp (measurable_pi_apply i))
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  exact lintegral_map' (hf i).aemeasurable (measurable_pi_apply i).aemeasurable |>.symm.trans
    (by rw [(measurePreserving_eval μ i).map_eq])

/-- The product of one-coordinate joint laws is the design-vector law followed
by the independent coordinate conditional laws. No conditional independence is assumed. -/
theorem pi_compProd_eq_map_pairVectors {ι α β : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    Measure.pi (fun i => (μ i).compProd (κ i)) =
      ((Measure.pi μ).compProd (finiteProductKernel κ)).map pairVectors := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply pairVectors_measurable (MeasurableSet.univ_pi hs),
    Measure.compProd_apply (pairVectors_measurable (MeasurableSet.univ_pi hs))]
  have hsection (x : ι → α) :
      Prod.mk x ⁻¹' (pairVectors ⁻¹' Set.univ.pi s) =
        Set.univ.pi (fun i => Prod.mk (x i) ⁻¹' s i) := by
    ext u
    simp [pairVectors, Set.mem_pi]
  simp_rw [hsection, finiteProductKernel_apply, Measure.pi_pi]
  rw [lintegral_coordinate_product μ
    (fun i a => κ i a (Prod.mk a ⁻¹' s i))
    (fun i => Kernel.measurable_kernel_prodMk_left (hs i))]
  simp_rw [Measure.compProd_apply (hs _)]

def designVectorLaw {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    Measure (Fin n → Covariate d) := Measure.pi (fun _ => designLaw θ)

def conditionalErrorLaw {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => θ.errors (x i))

def conditionalErrorKernel {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    Kernel (Fin n → Covariate d) (Fin n → ℝ) :=
  finiteProductKernel (fun _ => θ.errors)

instance conditionalErrorKernel_markov {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    IsMarkovKernel (conditionalErrorKernel θ n) := by
  unfold conditionalErrorKernel
  infer_instance

instance conditionalErrorLaw_probability {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) : IsProbabilityMeasure (conditionalErrorLaw θ x) := by
  unfold conditionalErrorLaw
  infer_instance

theorem conditionalErrorKernel_apply {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) : conditionalErrorKernel θ n x = conditionalErrorLaw θ x := rfl

/-- Reconstruct observations from the design and error vectors. -/
def samplesFromDesignErrors {d n : ℕ} (θ : RegressionParameter d)
    (z : (Fin n → Covariate d) × (Fin n → ℝ)) : Fin n → Observation d :=
  fun i => (z.1 i, θ.regression (z.1 i) + z.2 i)

theorem samplesFromDesignErrors_measurable {d n : ℕ} (θ : RegressionParameter d)
    (hf : Measurable θ.regression) : Measurable (samplesFromDesignErrors (n := n) θ) :=
  Measurable.of_eval (fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((hf.comp ((measurable_pi_apply i).comp measurable_fst)).add
        ((measurable_pi_apply i).comp measurable_snd)))

/-- An equality of the actual original sample measure, not an assumed conditional law. -/
theorem sampleLaw_eq_conditional_map {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (n : ℕ) :
    sampleLaw θ n =
      ((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)).map
        (samplesFromDesignErrors θ) := by
  let := designLaw_isProbability C θ hθ
  have hm : Measurable (fun z : Covariate d × ℝ =>
      (z.1, θ.regression z.1 + z.2)) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  have hp := pi_compProd_eq_map_pairVectors (ι := Fin n)
    (fun _ => designLaw θ) (fun _ => θ.errors)
  have hv : Measurable (fun z : Fin n → Covariate d × ℝ =>
      fun i => ((z i).1, θ.regression (z i).1 + (z i).2)) :=
    Measurable.of_eval (fun i => hm.comp (measurable_pi_apply i))
  unfold sampleLaw observationLaw
  rw [← Measure.pi_map_pi (fun _ => hm.aemeasurable), hp]
  rw [Measure.map_map hv pairVectors_measurable]
  rfl

/-- Tonelli's identity for any nonnegative measurable loss under the original law. -/
theorem sampleLaw_lintegral_conditioning {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : (Fin n → Observation d) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, g z ∂sampleLaw θ n) =
      ∫⁻ x, ∫⁻ u, g (samplesFromDesignErrors θ (x, u))
        ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
  let := designLaw_isProbability C θ hθ
  let : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => designLaw θ)))
  have hgm : Measurable (fun z : (Fin n → Covariate d) × (Fin n → ℝ) =>
      g (samplesFromDesignErrors θ z)) :=
    hg.comp (samplesFromDesignErrors_measurable θ hθ.2.1)
  rw [sampleLaw_eq_conditional_map C θ hθ,
    lintegral_map' hg.aemeasurable (samplesFromDesignErrors_measurable θ hθ.2.1).aemeasurable,
    Measure.lintegral_compProd hgm]
  rfl

/-- The paper's extended-valued mean square risk is exactly the conditional loss average. -/
theorem meanSquaredRisk_conditioning {d n : ℕ} (C : ModelConstants d)
    (T : Estimator d n) (θ : RegressionParameter d) (hθ : Admissible C θ) :
    meanSquaredRisk T θ =
      ∫⁻ x, ∫⁻ u, ENNReal.ofReal
        ((T.val (samplesFromDesignErrors θ (x, u)) - θ.variance) ^ 2)
        ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
  apply sampleLaw_lintegral_conditioning C θ hθ
  exact ENNReal.measurable_ofReal.comp ((T.property.sub measurable_const).pow_const 2)

/-- Bochner Fubini for every integrable vector-valued observation function. -/
theorem sampleLaw_integral_conditioning {d n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : (Fin n → Observation d) → E) (hg : Integrable g (sampleLaw θ n)) :
    (∫ z, g z ∂sampleLaw θ n) =
      ∫ x, ∫ u, g (samplesFromDesignErrors θ (x, u))
        ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
  let := designLaw_isProbability C θ hθ
  let : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => designLaw θ)))
  have hm := samplesFromDesignErrors_measurable (n := n) θ hθ.2.1
  have hmap : Integrable g
      (((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)).map
        (samplesFromDesignErrors θ)) := by
    rwa [← sampleLaw_eq_conditional_map C θ hθ]
  have hcomp : Integrable (fun z => g (samplesFromDesignErrors θ z))
      ((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)) := by
    simpa only [Function.comp_def] using hmap.comp_measurable hm
  rw [sampleLaw_eq_conditional_map C θ hθ,
    integral_map hm.aemeasurable hmap.aestronglyMeasurable,
    Measure.integral_compProd hcomp]
  rfl

/-- Original-law integrability implies integrability under almost every
conditional error law; this is derived from the actual measure identity. -/
theorem sampleLaw_integrable_conditionally {d n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : (Fin n → Observation d) → E) (hg : Integrable g (sampleLaw θ n)) :
    ∀ᵐ x ∂designVectorLaw θ n,
      Integrable (fun u => g (samplesFromDesignErrors θ (x, u)))
        (conditionalErrorLaw θ x) := by
  let := designLaw_isProbability C θ hθ
  let : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => designLaw θ)))
  have hmap : Integrable g
      (((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)).map
        (samplesFromDesignErrors θ)) := by
    rwa [← sampleLaw_eq_conditional_map C θ hθ]
  have hcomp := hmap.comp_measurable (samplesFromDesignErrors_measurable θ hθ.2.1)
  exact (Measure.integrable_compProd_iff hcomp.aestronglyMeasurable).mp hcomp |>.1

/-- Finite fourth moment gives actual fourth-power integrability of the coordinate. -/
theorem memLp_id_four_of_integrable_fourth (μ : Measure ℝ)
    (h4 : Integrable (fun u : ℝ => u ^ 4) μ) : MemLp (fun u : ℝ => u) 4 μ := by
  apply (integrable_norm_rpow_iff (f := fun u : ℝ => u) (p := 4)
    aestronglyMeasurable_id (by norm_num) (by simp)).mp
  have heq : (fun u : ℝ => ‖u‖ ^ ((4 : ℝ≥0∞).toReal)) = (fun u => u ^ 4) := by
    funext u
    norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    calc
      |u| ^ (4 : ℝ) = |u| ^ (4 : ℕ) := Real.rpow_natCast _ _
      _ = |u ^ 4| := (abs_pow u 4).symm
      _ = u ^ 4 := abs_of_nonneg (by positivity)
  rw [heq]
  exact h4

theorem conditionalErrorLaw_iIndepFun {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) :
    iIndepFun (fun i (u : Fin n → ℝ) => u i) (conditionalErrorLaw θ x) :=
  iIndepFun_pi (μ := fun i => θ.errors (x i)) (X := fun _ => id)
    (fun _ => aemeasurable_id)

theorem conditionalErrorLaw_integral_coordinate {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) (i : Fin n) (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ u, g (u i) ∂conditionalErrorLaw θ x) = ∫ a, g a ∂θ.errors (x i) := by
  have hm := (measurePreserving_eval (fun j => θ.errors (x j)) i).map_eq
  have h := integral_map (μ := Measure.pi (fun j => θ.errors (x j)))
    (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable
  rw [hm] at h
  exact h.symm

theorem unitCube_measurable (d : ℕ) : MeasurableSet (unitCube d) := by
  have heq : unitCube d = Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [unitCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      true_imp_iff, Set.mem_Icc]
  rw [heq]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- The design law is supported on the actual cube, even before admissibility. -/
theorem designLaw_cube_ae {d : ℕ} (θ : RegressionParameter d) :
    ∀ᵐ x ∂designLaw θ, x ∈ unitCube d := by
  have hx : ∀ᵐ x ∂cubeVolume d, x ∈ unitCube d :=
    ae_restrict_mem (unitCube_measurable d)
  exact hx.filter_mono (withDensity_absolutelyContinuous (cubeVolume d)
    (fun x => ENNReal.ofReal (θ.density x))).ae_le

/-- All fixed-design hypotheses used by projection risk bounds follow from
admissibility for almost every vector of iid design points. -/
theorem admissible_conditional_error_facts {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (n : ℕ) :
    ∀ᵐ x ∂designVectorLaw θ n,
      (∀ i, x i ∈ unitCube d) ∧
      (∀ i, MemLp (fun u : Fin n → ℝ => u i) 4 (conditionalErrorLaw θ x)) ∧
      iIndepFun (fun i (u : Fin n → ℝ) => u i) (conditionalErrorLaw θ x) ∧
      (∀ i, (∫ u, u i ∂conditionalErrorLaw θ x) = 0) ∧
      (∀ i, (∫ u, (u i) ^ 2 ∂conditionalErrorLaw θ x) = θ.variance) ∧
      (∀ i, (∫ u, (u i) ^ 4 ∂conditionalErrorLaw θ x) ≤ C.fourthBound) := by
  let := designLaw_isProbability C θ hθ
  have hbase := (designLaw_cube_ae θ).and hθ.2.2.2.2.2.2.2
  have hgood : ∀ᵐ x ∂designVectorLaw θ n, ∀ i,
      x i ∈ unitCube d ∧
      Integrable (fun u : ℝ => u) (θ.errors (x i)) ∧
      Integrable (fun u : ℝ => u ^ 2) (θ.errors (x i)) ∧
      Integrable (fun u : ℝ => u ^ 4) (θ.errors (x i)) ∧
      (∫ u : ℝ, u ∂θ.errors (x i)) = 0 ∧
      (∫ u : ℝ, u ^ 2 ∂θ.errors (x i)) = θ.variance ∧
      (∫ u : ℝ, u ^ 4 ∂θ.errors (x i)) ≤ C.fourthBound := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => designLaw θ) (i := i)).eventually hbase
  filter_upwards [hgood] with x hx
  refine ⟨fun i => (hx i).1, ?_, conditionalErrorLaw_iIndepFun θ x, ?_, ?_, ?_⟩
  · intro i
    have h4 := (hx i).2.2.2.1
    simpa only [Function.comp_def, Function.eval, conditionalErrorLaw] using
      (memLp_id_four_of_integrable_fourth (θ.errors (x i)) h4).comp_measurePreserving
        (measurePreserving_eval (fun j => θ.errors (x j)) i)
  · intro i
    rw [conditionalErrorLaw_integral_coordinate θ x i (fun u => u) measurable_id]
    exact (hx i).2.2.2.2.1
  · intro i
    rw [conditionalErrorLaw_integral_coordinate θ x i (fun u => u ^ 2) (by fun_prop)]
    exact (hx i).2.2.2.2.2.1
  · intro i
    rw [conditionalErrorLaw_integral_coordinate θ x i (fun u => u ^ 4) (by fun_prop)]
    exact (hx i).2.2.2.2.2.2

end NearlyMinimax
