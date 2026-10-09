module

public import NearlyMinimax.FinePairReference
public import NearlyMinimax.BoundedHyperplaneField
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd


@[expose] public section

/-! The fine density packet with the actual bounded hyperplane field,
and the genuine Lebesgue-time/field carrier of the coarse and fine rows. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev FinePairFieldMark (d : ℕ) := partitionFieldMark (Covariate d × ℝ)

def finePairHyperplaneDensity (d : ℕ) (T a b : ℝ) (M : ℕ) :
    SignedMeasure (FinePairFieldMark d × FinePairDensityIndex M) :=
  finePairFieldSignedMeasure (boundedHyperplaneFieldLaw d T) a b M

def finePairHyperplaneReset {d : ℕ} (a b : ℝ) (M : ℕ) (p : Covariate d → ℝ)
    (e : FinePairFieldMark d × FinePairDensityIndex M) (u : Covariate d) : ℝ :=
  finePairFieldReset a b M p boundedHyperplaneFieldValue e u

theorem boundedHyperplaneFieldValue_section_measurable (d : ℕ) (u : Covariate d) :
    Measurable (fun z : FinePairFieldMark d => boundedHyperplaneFieldValue z u) :=
  (boundedHyperplaneFieldValue_measurable d).comp (measurable_id.prodMk measurable_const)

theorem finePairHyperplaneReset_interval {d : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) (p : Covariate d → ℝ) (hp : ∀ u, p u ∈ Icc a b)
    (e : FinePairFieldMark d × FinePairDensityIndex M) (u : Covariate d) :
    finePairHyperplaneReset a b M p e u ∈ Icc a b :=
  finePairFieldReset_mem_interval a b ha hab M p hp boundedHyperplaneFieldValue
    (fun z u => (boundedHyperplaneFieldValue_abs z u).le) e u

theorem finePairHyperplaneDensity_totalVariation (d : ℕ) [NeZero d]
    (T a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    ((finePairHyperplaneDensity d T a b M).variation univ).toReal =
      2 * |finePairDensityPrefactor a b| *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) :=
  finePairFieldSignedMeasure_totalVariation (boundedHyperplaneFieldLaw d T) a b ha hab M

theorem finePairHyperplaneDensity_mass_zero (d : ℕ) [NeZero d] (T a b : ℝ) (M : ℕ) :
    (∫ᵛ _e, (1 : ℝ) ∂<•finePairHyperplaneDensity d T a b M) = 0 :=
  finePairFieldSignedMeasure_mass_zero (boundedHyperplaneFieldLaw d T) a b M

theorem finePairHyperplaneDensity_linear_zero (d : ℕ) [NeZero d]
    (T a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ)
    (p : Covariate d → ℝ) (hp : ∀ u, p u ∈ Icc a b) (u : Covariate d) :
    (∫ᵛ e, finePairHyperplaneReset a b M p e u
      ∂<•finePairHyperplaneDensity d T a b M) = 0 :=
  finePairFieldSignedMeasure_linear_zero (boundedHyperplaneFieldLaw d T) a b ha hab M p hp
    boundedHyperplaneFieldValue (boundedHyperplaneFieldValue_section_measurable d)
    (fun z u => (boundedHyperplaneFieldValue_abs z u).le) u

theorem finePairHyperplaneDensity_pair (d : ℕ) [NeZero d]
    (T : ℝ) (hT : 0 ≤ T) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) (hM : 2 ≤ M) (p : Covariate d → ℝ) (hp : ∀ u, p u ∈ Icc a b)
    (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ᵛ e, finePairHyperplaneReset a b M p e u * finePairHyperplaneReset a b M p e v
      ∂<•finePairHyperplaneDensity d T a b M) =
      p u * p v * Real.exp (-T * euclideanNorm (fun r => u r - v r)) := by
  change (∫ᵛ e, finePairFieldReset a b M p boundedHyperplaneFieldValue e u *
      finePairFieldReset a b M p boundedHyperplaneFieldValue e v
      ∂<•finePairFieldSignedMeasure (boundedHyperplaneFieldLaw d T) a b M) = _
  rw [finePairFieldSignedMeasure_pair_exact (boundedHyperplaneFieldLaw d T) a b ha hab M hM p hp
    boundedHyperplaneFieldValue (boundedHyperplaneFieldValue_section_measurable d)
    (fun z u => (boundedHyperplaneFieldValue_abs z u).le),
    boundedHyperplaneField_covariance d T hT u v hu hv]

def finePairFieldKernel (d : ℕ) : Kernel ℝ (FinePairFieldMark d) where
  toFun := boundedHyperplaneFieldLaw d
  measurable' := boundedHyperplaneFieldLaw_measurable d

instance finePairFieldKernel_markov (d : ℕ) [NeZero d] : IsMarkovKernel (finePairFieldKernel d) :=
  ⟨fun T => boundedHyperplaneFieldLaw_probability d T⟩

def finePairTimeFieldMeasure (d : ℕ) (lo hi : ℝ) : Measure (ℝ × FinePairFieldMark d) :=
  (volume.restrict (Icc lo hi)).compProd (finePairFieldKernel d)

instance finePairTimeFieldMeasure_finite (d : ℕ) [NeZero d] (lo hi : ℝ) :
    IsFiniteMeasure (finePairTimeFieldMeasure d lo hi) := by
  unfold finePairTimeFieldMeasure
  infer_instance

theorem finePairTimeFieldMeasure_integral (d : ℕ) [NeZero d] (lo hi : ℝ)
    (f : ℝ × FinePairFieldMark d → ℝ) (hf : Integrable f (finePairTimeFieldMeasure d lo hi)) :
    (∫ e, f e ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, ∫ z, f (T,z) ∂boundedHyperplaneFieldLaw d T :=
  Measure.integral_compProd hf

def finePairTimeFieldValue {d : ℕ} (e : ℝ × FinePairFieldMark d) (u : Covariate d) : ℝ :=
  boundedHyperplaneFieldValue e.2 u

theorem finePairTimeFieldValue_measurable (d : ℕ) :
    Measurable (fun ex : (ℝ × FinePairFieldMark d) × Covariate d =>
      finePairTimeFieldValue ex.1 ex.2) :=
  (boundedHyperplaneFieldValue_measurable d).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem finePairTimeFieldValue_abs {d : ℕ} (e : ℝ × FinePairFieldMark d) (u : Covariate d) :
    |finePairTimeFieldValue e u| = 1 := boundedHyperplaneFieldValue_abs _ _

theorem finePairTimeFieldMeasure_ae_time (d : ℕ) [NeZero d] (lo hi : ℝ) :
    ∀ᵐ e ∂finePairTimeFieldMeasure d lo hi, e.1 ∈ Icc lo hi :=
  Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
    (ae_restrict_mem measurableSet_Icc)

theorem finePairTimeFieldMeasure_fst_integrable (d : ℕ) [NeZero d] (lo hi : ℝ) :
    Integrable (fun e : ℝ × FinePairFieldMark d => e.1) (finePairTimeFieldMeasure d lo hi) := by
  apply (integrable_const (max |lo| |hi|)).mono' measurable_fst.aestronglyMeasurable
  filter_upwards [finePairTimeFieldMeasure_ae_time d lo hi] with e he
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [neg_abs_le lo, le_max_left |lo| |hi|, he.1],
    by linarith [le_abs_self hi, le_max_right |lo| |hi|, he.2]⟩

theorem finePairTimeFieldMeasure_fst_integral (d : ℕ) [NeZero d] (lo hi : ℝ) :
    (∫ e : ℝ × FinePairFieldMark d, e.1 ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T := by
  rw [finePairTimeFieldMeasure_integral d lo hi _ (finePairTimeFieldMeasure_fst_integrable d lo hi)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul]

section Matrix
variable {ι : Type*} [Fintype ι]

def finePairTimeMatrix (d : ℕ) (A : ι → ι → ℝ) (e : ℝ × FinePairFieldMark d) : ι → ι → ℝ :=
  fun i j => e.1 * A i j

theorem finePairTimeMatrix_measurable (d : ℕ) (A : ι → ι → ℝ) (i j : ι) :
    Measurable (fun e => finePairTimeMatrix d A e i j) := measurable_fst.mul_const _

theorem finePairTimeMatrix_cost (d : ℕ) (A : ι → ι → ℝ) (e : ℝ × FinePairFieldMark d) :
    separatedMatrixCost (finePairTimeMatrix d A) e =
      |e.1| * (∑ i, ∑ j, |A i j|) := by
  simp only [separatedMatrixCost, finePairTimeMatrix, abs_mul, Finset.mul_sum]

theorem finePairTimeMatrix_cost_integrable (d : ℕ) [NeZero d] (lo hi : ℝ) (A : ι → ι → ℝ) :
    Integrable (separatedMatrixCost (finePairTimeMatrix d A)) (finePairTimeFieldMeasure d lo hi) := by
  change Integrable (fun e => separatedMatrixCost (finePairTimeMatrix d A) e) _
  simp only [finePairTimeMatrix_cost]
  exact (finePairTimeFieldMeasure_fst_integrable d lo hi).abs.mul_const _

end Matrix

theorem finePairTimeFieldValue_pair_integrable (d : ℕ) [NeZero d] (lo hi : ℝ)
    (u v : Covariate d) :
    Integrable (fun e => finePairTimeFieldValue e u * finePairTimeFieldValue e v)
      (finePairTimeFieldMeasure d lo hi) := by
  have hm (u : Covariate d) : Measurable (fun e : ℝ × FinePairFieldMark d =>
      finePairTimeFieldValue e u) :=
    (boundedHyperplaneFieldValue_section_measurable d u).comp measurable_snd
  apply (integrable_const (1 : ℝ)).mono' ((hm u).mul (hm v)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun e => by
    change ‖finePairTimeFieldValue e u * finePairTimeFieldValue e v‖ ≤ 1
    simp only [Real.norm_eq_abs, abs_mul, finePairTimeFieldValue_abs, one_mul, le_refl])

theorem finePairTimeFieldValue_weighted_pair_integrable (d : ℕ) [NeZero d] (lo hi : ℝ)
    (u v : Covariate d) :
    Integrable (fun e => e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v))
      (finePairTimeFieldMeasure d lo hi) := by
  have hm (u : Covariate d) : Measurable (fun e : ℝ × FinePairFieldMark d =>
      finePairTimeFieldValue e u) :=
    (boundedHyperplaneFieldValue_section_measurable d u).comp measurable_snd
  exact (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
    ((hm u).mul (hm v)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      change ‖finePairTimeFieldValue e u * finePairTimeFieldValue e v‖ ≤ 1
      simp only [Real.norm_eq_abs, abs_mul, finePairTimeFieldValue_abs, one_mul, le_refl]))

theorem finePairTimeFieldValue_weighted_covariance (d : ℕ) [NeZero d] (lo hi : ℝ)
    (hlo : 0 ≤ lo) (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ e, e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)
      ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm (fun r => u r - v r)) := by
  rw [finePairTimeFieldMeasure_integral d lo hi _
    (finePairTimeFieldValue_weighted_pair_integrable d lo hi u v)]
  simp only [finePairTimeFieldValue, integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
  rw [boundedHyperplaneField_covariance d T (hlo.trans hT.1) u v hu hv]

end NearlyMinimax
