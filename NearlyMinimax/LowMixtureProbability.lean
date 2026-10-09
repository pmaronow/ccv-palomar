module

public import NearlyMinimax.LowSmoothnessGridExperiment
public import NearlyMinimax.PathRisk


@[expose] public section

/-! Actual augmented design--activation--response probability measures.
The conditional finite weights and scores are those of the low-smoothness
experiment. Markov normalization and all integral identities are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev LowMixtureMarks (m n : ℕ) := (Fin m → Fin 3) × (Fin n → Fin 3)

def lowMixtureWeight {α : Type*} (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (x : α)
    (z : LowMixtureMarks m n) : ℝ :=
  activationProductPrior m t z.1 * finiteResponseLikelihood m n a V (f x) z.1 z.2

theorem lowMixtureWeight_measurable {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (z : LowMixtureMarks m n) :
    Measurable (fun x => lowMixtureWeight m n a V t f x z) := by
  unfold lowMixtureWeight finiteResponseLikelihood
  exact (Finset.measurable_prod _ (fun i _ =>
    ternaryMass_measurable_comp a V _ (hf z.1 i) (z.2 i))).const_mul _

def lowMixtureIndexKernel {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) : Kernel α (LowMixtureMarks m n) where
  toFun x := ∑ z : LowMixtureMarks m n,
    ENNReal.ofReal (lowMixtureWeight m n a V t f x z) • Measure.dirac z
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun z _ =>
      (ENNReal.measurable_ofReal.comp (lowMixtureWeight_measurable m n a V t f hf z)).mul_const _)

theorem lowMixtureIndexKernel_apply {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (x : α) :
    lowMixtureIndexKernel m n a V t f hf x =
      ∑ z : LowMixtureMarks m n,
        ENNReal.ofReal (lowMixtureWeight m n a V t f x z) • Measure.dirac z := rfl

theorem lowMixtureWeight_nonneg {α : Type*} (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) (x : α) (z : LowMixtureMarks m n) :
    0 ≤ lowMixtureWeight m n a V t f x z :=
  finite_experiment_joint_nonnegative m n a V t (f x) ht.1 ht.2 (hp x) z.1 z.2

theorem lowMixtureIndexKernel_markov {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) :
    IsMarkovKernel (lowMixtureIndexKernel m n a V t f hf) := by
  constructor
  intro x
  constructor
  simp only [lowMixtureIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
    lowMixtureWeight_nonneg m n a V t f ht hp x z)]
  simp only [lowMixtureWeight, Fintype.sum_prod_type]
  rw [finite_experiment_joint_normalized m n a V t (f x) ha]
  simp

theorem lowMixtureIndexKernel_lintegral {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (x : α)
    (H : LowMixtureMarks m n → ℝ≥0∞) :
    (∫⁻ z, H z ∂lowMixtureIndexKernel m n a V t f hf x) =
      ∑ ξ, ∑ y, ENNReal.ofReal (activationProductPrior m t ξ *
        finiteResponseLikelihood m n a V (f x) ξ y) * H (ξ, y) := by
  simp [lowMixtureIndexKernel_apply, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul, lowMixtureWeight, Fintype.sum_prod_type]

theorem lowMixtureIndexKernel_integral {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (x : α) (H : LowMixtureMarks m n → ℝ) :
    (∫ z, H z ∂lowMixtureIndexKernel m n a V t f hf x) =
      ∑ ξ, activationProductPrior m t ξ *
        ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (ξ, y) := by
  rw [lowMixtureIndexKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      lowMixtureWeight, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have hpos : 0 ≤ activationProductPrior m t ξ * finiteResponseLikelihood m n a V (f x) ξ y :=
      lowMixtureWeight_nonneg m n a V t f ht hp x (ξ, y)
    rw [ENNReal.toReal_ofReal hpos]
    ring
  · intro z hz
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

def lowMixtureLaw {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) : Measure (α × LowMixtureMarks m n) :=
  μ.compProd (lowMixtureIndexKernel m n a V t f hf)

theorem lowMixtureLaw_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) :
    IsProbabilityMeasure (lowMixtureLaw μ m n a V t f hf) := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  unfold lowMixtureLaw
  infer_instance

theorem lowMixtureLaw_lintegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∫⁻ x, ∑ ξ, ∑ y, ENNReal.ofReal (activationProductPrior m t ξ *
        finiteResponseLikelihood m n a V (f x) ξ y) * H (x, ξ, y) ∂μ := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  rw [lowMixtureLaw, Measure.lintegral_compProd hH]
  simp_rw [lowMixtureIndexKernel_lintegral]

theorem lowMixtureLaw_integrable_of_weighted_norm {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ) (hH : Measurable H)
    (hNorm : Integrable (fun x => ∑ ξ, activationProductPrior m t ξ *
      ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * |H (x, ξ, y)|) μ) :
    Integrable H (lowMixtureLaw μ m n a V t f hf) := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  unfold lowMixtureLaw
  apply (Measure.integrable_compProd_iff hH.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun x => Integrable.of_finite)
  · simp_rw [lowMixtureIndexKernel_integral m n a V t f hf ht hp,
      Real.norm_eq_abs]
    exact hNorm

theorem lowMixtureLaw_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ)
    (hH : Integrable H (lowMixtureLaw μ m n a V t f hf)) :
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∫ x, ∑ ξ, activationProductPrior m t ξ *
        ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  rw [lowMixtureLaw, Measure.integral_compProd hH]
  simp_rw [lowMixtureIndexKernel_integral m n a V t f hf ht hp]

theorem finiteResponseLikelihood_measurable_comp {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    Measurable (fun x => finiteResponseLikelihood m n a V (f x) ξ y) := by
  unfold finiteResponseLikelihood
  exact Finset.measurable_prod _ (fun i _ =>
    ternaryMass_measurable_comp a V _ (hf ξ i) (y i))

theorem finiteExperimentScore_measurable_comp {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V η : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    Measurable (fun x => finiteExperimentScore m n a V η (f x) ξ y) := by
  have hL := finiteResponseLikelihood_measurable_comp m n a V f hf
  have hU (i : Fin n) : Measurable (fun x =>
      finiteResponseVarianceTerm m n a V (f x) ξ y i) := by
    unfold finiteResponseVarianceTerm
    exact (Finset.measurable_prod _ (fun l _ =>
      ternaryMass_measurable_comp a V _ (hf ξ l) (y l))).const_mul _
  have hD (j : Fin m) : Measurable (fun x => latentDifference m j
      (fun ξ' => finiteResponseLikelihood m n a V (f x) ξ' y) ξ) := by
    unfold latentDifference
    exact (((hL (Function.update ξ j 2) y).const_mul (1 / 2)).add
      ((hL (Function.update ξ j 0) y).const_mul (1 / 2))).sub
        (hL (Function.update ξ j 1) y)
  unfold finiteExperimentScore finiteExperimentScoreNumerator
  exact ((Finset.measurable_sum _ (fun j _ => hD j)).sub
    ((Finset.measurable_sum _ (fun i _ => hU i)).const_mul (η ^ 2))).div (hL ξ y)

def lowMixtureScore {α : Type*} (m n : ℕ) (a V η : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (z : α × LowMixtureMarks m n) : ℝ :=
  finiteExperimentScore m n a V η (f z.1) z.2.1 z.2.2

theorem lowMixtureScore_measurable {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V η : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) :
    Measurable (lowMixtureScore m n a V η f) := by
  apply measurable_from_prod_countable_left
  intro z
  exact finiteExperimentScore_measurable_comp m n a V η f hf z.1 z.2

def lowMixtureConditionalScoreEnergy {α : Type*} (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (x : α) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ * ∑ y,
    finiteResponseLikelihood m n a V (f x) ξ y *
      finiteExperimentScore m n a V η (f x) ξ y ^ 2

theorem lowMixtureConditionalScoreEnergy_measurable {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V η t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) :
    Measurable (lowMixtureConditionalScoreEnergy m n a V η t f) := by
  unfold lowMixtureConditionalScoreEnergy
  exact Finset.measurable_sum _ (fun ξ _ => (Finset.measurable_sum _ (fun y _ =>
    (finiteResponseLikelihood_measurable_comp m n a V f hf ξ y).mul
      ((finiteExperimentScore_measurable_comp m n a V η f hf ξ y).pow_const 2))).const_mul _)

theorem lowMixtureScore_sq_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ) :
    Integrable (fun z => lowMixtureScore m n a V η f z ^ 2)
      (lowMixtureLaw μ m n a V t f hf) := by
  apply lowMixtureLaw_integrable_of_weighted_norm μ m n a V t f hf ha ht hp _
    ((lowMixtureScore_measurable m n a V η f hf).pow_const 2)
  have heq : (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y *
        |lowMixtureScore m n a V η f (x, ξ, y) ^ 2|) =
      lowMixtureConditionalScoreEnergy m n a V η t f := by
    funext x
    unfold lowMixtureConditionalScoreEnergy
    apply Finset.sum_congr rfl
    intro ξ hξ
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [abs_of_nonneg (sq_nonneg _)]
    rfl
  rw [heq]
  exact hE

theorem lowMixtureScore_memLp_two {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ) :
    MemLp (lowMixtureScore m n a V η f) 2 (lowMixtureLaw μ m n a V t f hf) :=
  (memLp_two_iff_integrable_sq (lowMixtureScore_measurable m n a V η f hf).aestronglyMeasurable).mpr
    (lowMixtureScore_sq_integrable μ m n a V η t f hf ha ht hp hE)

theorem lowMixtureScore_sq_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ) :
    (∫ z, lowMixtureScore m n a V η f z ^ 2 ∂lowMixtureLaw μ m n a V t f hf) =
      ∫ x, lowMixtureConditionalScoreEnergy m n a V η t f x ∂μ := by
  exact lowMixtureLaw_integral μ m n a V t f hf ha ht hp _
    (lowMixtureScore_sq_integrable μ m n a V η t f hf ha ht hp hE)

theorem lowMixtureIndexKernel_score_centered {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V η t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 < ternaryMass a (f x ξ i) V y)
    (x : α) :
    (∫ z, lowMixtureScore m n a V η f (x, z)
      ∂lowMixtureIndexKernel m n a V t f hf x) = 0 := by
  rw [lowMixtureIndexKernel_integral m n a V t f hf ht
    (fun x ξ i y => (hp x ξ i y).le)]
  unfold lowMixtureScore
  have hc (ξ : Fin m → Fin 3) := finite_experiment_score_centered m n a V η (f x) ξ ha
    (fun y => Finset.prod_pos (fun i _ => hp x ξ i (y i)))
  simp_rw [hc, mul_zero]
  simp

theorem lowMixtureScore_centered {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 < ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ) :
    (∫ z, lowMixtureScore m n a V η f z ∂lowMixtureLaw μ m n a V t f hf) = 0 := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht (fun x ξ i y => (hp x ξ i y).le)
  let := lowMixtureLaw_probability μ m n a V t f hf ha ht (fun x ξ i y => (hp x ξ i y).le)
  have hi := (lowMixtureScore_memLp_two μ m n a V η t f hf ha ht
    (fun x ξ i y => (hp x ξ i y).le) hE).integrable (by norm_num)
  rw [lowMixtureLaw, Measure.integral_compProd hi]
  simp_rw [lowMixtureIndexKernel_score_centered m n a V η t f hf ha ht hp]
  simp

/-- Integrate the design first in each latent state, with all integrability
hypotheses stated on genuine finite response expectations. -/
theorem lowMixtureLaw_integral_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ)
    (hH : Integrable H (lowMixtureLaw μ m n a V t f hf))
    (hξ : ∀ ξ, Integrable (fun x => ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y)) μ) :
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∑ ξ, activationProductPrior m t ξ *
        ∫ x, ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  rw [lowMixtureLaw_integral μ m n a V t f hf ha ht hp H hH,
    integral_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _)]
  simp_rw [integral_const_mul]

theorem lowMixtureLaw_nonneg_integral_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ) (hH : Measurable H) (hnonneg : ∀ z, 0 ≤ H z)
    (hξ : ∀ ξ, Integrable (fun x => ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y)) μ) :
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∑ ξ, activationProductPrior m t ξ *
        ∫ x, ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  have hNorm : Integrable (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y * |H (x, ξ, y)|) μ := by
    have heq : (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a V (f x) ξ y * |H (x, ξ, y)|) =
        (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
          finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y)) := by
      funext x
      apply Finset.sum_congr rfl
      intro ξ hξ
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [abs_of_nonneg (hnonneg (x, ξ, y))]
    rw [heq]
    exact integrable_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _)
  exact lowMixtureLaw_integral_sum μ m n a V t f hf ha ht hp H
    (lowMixtureLaw_integrable_of_weighted_norm μ m n a V t f hf ha ht hp H hH hNorm) hξ

theorem lowMixtureConditionalScoreEnergy_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hξ : ∀ ξ, Integrable (fun x => ∑ y, finiteResponseLikelihood m n a V (f x) ξ y *
      finiteExperimentScore m n a V η (f x) ξ y ^ 2) μ) :
    Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ :=
  integrable_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _)

theorem lowMixtureScore_sq_integral_eq_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hξ : ∀ ξ, Integrable (fun x => ∑ y, finiteResponseLikelihood m n a V (f x) ξ y *
      finiteExperimentScore m n a V η (f x) ξ y ^ 2) μ) :
    (∫ z, lowMixtureScore m n a V η f z ^ 2 ∂lowMixtureLaw μ m n a V t f hf) =
      ∑ ξ, activationProductPrior m t ξ * ∫ x,
        ∑ y, finiteResponseLikelihood m n a V (f x) ξ y *
          finiteExperimentScore m n a V η (f x) ξ y ^ 2 ∂μ := by
  apply lowMixtureLaw_integral_sum μ m n a V t f hf ha ht hp _
    (lowMixtureScore_sq_integrable μ m n a V η t f hf ha ht hp
      (lowMixtureConditionalScoreEnergy_integrable μ m n a V η t f hξ))
  exact hξ

end NearlyMinimax
