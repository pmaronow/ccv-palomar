module

public import NearlyMinimax.GaussianHyperplaneGeometry
public import NearlyMinimax.GaussianProjectionMean
public import NearlyMinimax.PoissonCellMomentBounds


@[expose] public section

/-! The actual bounded Gaussian-hyperplane cell field: a Borel probability
law with exact exponential Euclidean covariance and vanishing odd moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem hyperplaneNormalizingConstant_actual (d : ℕ) :
    hyperplaneNormalizingConstant d = 2 * d * gaussianAbsoluteMean :=
  hyperplaneNormalizingConstant_eq d

theorem hyperplaneNormalizingConstant_pos (d : ℕ) [NeZero d] :
    0 < hyperplaneNormalizingConstant d := by
  rw [hyperplaneNormalizingConstant_actual]
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (NeZero.pos d))) gaussianAbsoluteMean_pos

def gaussianHyperplaneLaw (d : ℕ) : Measure (Covariate d × ℝ) :=
  (ENNReal.ofReal (hyperplaneNormalizingConstant d))⁻¹ • gaussianHyperplaneIntensity d

instance gaussianHyperplaneLaw_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (gaussianHyperplaneLaw d) := by
  constructor
  rw [gaussianHyperplaneLaw, Measure.smul_apply, smul_eq_mul,
    gaussianHyperplaneIntensity_univ_ofReal]
  exact ENNReal.inv_mul_cancel (by simp [hyperplaneNormalizingConstant_pos d])
    ENNReal.ofReal_ne_top

theorem gaussianPhase_sub {d : ℕ} (u v Z : Covariate d) :
    gaussianPhase u Z - gaussianPhase v Z = gaussianPhase (fun r => u r - v r) Z := by
  simp only [gaussianPhase, sub_mul, Finset.sum_sub_distrib]

theorem gaussianHyperplaneLaw_separation_real (d : ℕ) [NeZero d] (u v : Covariate d)
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (gaussianHyperplaneLaw d).real (hyperplaneSeparationSet u v) =
      euclideanNorm (fun r => u r - v r) / (2 * d) := by
  rw [gaussianHyperplaneLaw, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hyperplaneNormalizingConstant_pos d).le]
  rw [measureReal_def, gaussianHyperplaneIntensity_separation_ofReal u v hu hv]
  have hi : 0 ≤ ∫ Z, |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d :=
    integral_nonneg (fun _ => abs_nonneg _)
  rw [ENNReal.toReal_ofReal hi]
  simp_rw [gaussianPhase_sub]
  rw [gaussianPhase_abs_integral, hyperplaneNormalizingConstant_actual]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hg := gaussianAbsoluteMean_pos.ne'
  field_simp

theorem gaussianHyperplaneLaw_same_complement (d : ℕ) [NeZero d] (u v : Covariate d) :
    1 - partitionSameProbability (gaussianHyperplaneLaw d) hyperplaneHalfspace u v =
      (gaussianHyperplaneLaw d).real (hyperplaneSeparationSet u v) := by
  let s : Set (Covariate d × ℝ) := {h | hyperplaneHalfspace h u = hyperplaneHalfspace h v}
  have hs : MeasurableSet s := (hyperplaneSeparationSet_measurable u v).of_compl
  have he : partitionSameProbability (gaussianHyperplaneLaw d) hyperplaneHalfspace u v =
      (gaussianHyperplaneLaw d).real s := by
    simpa only [partitionSameProbability, s, Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using
      (integral_indicator_one (μ := gaussianHyperplaneLaw d) hs)
  rw [he]
  change 1 - (gaussianHyperplaneLaw d).real s = (gaussianHyperplaneLaw d).real sᶜ
  rw [measureReal_compl hs]
  simp

def boundedHyperplaneFieldLaw (d : ℕ) (T : ℝ) : Measure (partitionFieldMark (Covariate d × ℝ)) :=
  poissonCellFieldLaw (gaussianHyperplaneLaw d) (Real.toNNReal (2 * d * T))

def boundedHyperplaneFieldValue {d : ℕ} (z : partitionFieldMark (Covariate d × ℝ))
    (u : Covariate d) : ℝ := poissonCellFieldValue hyperplaneHalfspace z u

instance boundedHyperplaneFieldLaw_probability (d : ℕ) [NeZero d] (T : ℝ) :
    IsProbabilityMeasure (boundedHyperplaneFieldLaw d T) := by
  unfold boundedHyperplaneFieldLaw
  infer_instance

theorem boundedHyperplaneFieldLaw_measurable (d : ℕ) :
    Measurable (boundedHyperplaneFieldLaw d) := by
  exact (poissonCellFieldLaw_measurable (gaussianHyperplaneLaw d)).comp
    (measurable_real_toNNReal.comp (measurable_const.mul measurable_id))

theorem boundedHyperplaneFieldValue_measurable (d : ℕ) :
    Measurable (fun z : partitionFieldMark (Covariate d × ℝ) × Covariate d =>
      boundedHyperplaneFieldValue z.1 z.2) :=
  poissonCellFieldValue_measurable hyperplaneHalfspace hyperplaneHalfspace_measurable

theorem boundedHyperplaneFieldValue_abs {d : ℕ}
    (z : partitionFieldMark (Covariate d × ℝ)) (u : Covariate d) :
    |boundedHyperplaneFieldValue z u| = 1 := poissonCellFieldValue_abs _ _ _

theorem boundedHyperplaneField_covariance (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 ≤ T)
    (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ z, boundedHyperplaneFieldValue z u * boundedHyperplaneFieldValue z v
      ∂boundedHyperplaneFieldLaw d T) =
      Real.exp (-T * euclideanNorm (fun r => u r - v r)) := by
  simp only [boundedHyperplaneFieldLaw, boundedHyperplaneFieldValue]
  rw [poissonCellField_covariance _ _ _ hyperplaneHalfspace_measurable,
    gaussianHyperplaneLaw_same_complement, gaussianHyperplaneLaw_separation_real d u v hu hv]
  rw [Real.coe_toNNReal (2 * (d : ℝ) * T) (by positivity)]
  congr 1
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

theorem boundedHyperplaneField_odd_moment (d : ℕ) [NeZero d] (T : ℝ) (j : ℕ)
    (U : Fin j → Covariate d) (hj : Odd j) :
    (∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T) = 0 :=
  poissonCellField_odd_moment _ _ hyperplaneHalfspace hyperplaneHalfspace_measurable j U hj

theorem boundedHyperplaneField_higher_moment_envelope (d : ℕ) [NeZero d]
    (T : ℝ) (hT : 0 ≤ T) (j : ℕ) (hj : 4 ≤ j) (U : Fin j → Covariate d)
    (hU : ∀ l, U l ∈ hyperplaneCube d) :
    |∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 *
        (euclideanNorm (fun r => U (q.val 0) r - U (q.val 1) r) +
          euclideanNorm (fun r => U (q.val 2) r - U (q.val 3) r))) := by
  have hb := poissonCellField_product_moment_abs_le_two_pairs (gaussianHyperplaneLaw d)
    (Real.toNNReal (2 * d * T)) hyperplaneHalfspace hyperplaneHalfspace_measurable j hj U
  change |∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T| ≤ _ at hb
  apply hb.trans_eq
  apply Finset.sum_congr rfl
  intro q _
  rw [gaussianHyperplaneLaw_same_complement, gaussianHyperplaneLaw_same_complement,
    gaussianHyperplaneLaw_separation_real d _ _ (hU _) (hU _),
    gaussianHyperplaneLaw_separation_real d _ _ (hU _) (hU _),
    Real.coe_toNNReal (2 * (d : ℝ) * T) (by positivity)]
  congr 1
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

end NearlyMinimax
