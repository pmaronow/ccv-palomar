module

public import NearlyMinimax.BoundedHyperplaneField
public import NearlyMinimax.SpatialLaplaceTail
public import NearlyMinimax.SpatialPairProductIntegration
public import Mathlib.Algebra.Order.Chebyshev


@[expose] public section

/-! Actual spatial L² moments of the constructed bounded hyperplane field.
The estimate derives from its fair-sign occupancy law and genuine independent
spatial-coordinate integration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def boundedHyperplaneSpatialMoment (d : ℕ) (T : ℝ) (j : ℕ)
    (U : Fin j → Covariate d) : ℝ :=
  ∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T

theorem boundedHyperplaneSpatialMoment_measurable (d : ℕ) [NeZero d] (T : ℝ) (j : ℕ) :
    Measurable (boundedHyperplaneSpatialMoment d T j) := by
  have hm : Measurable (fun Uz : (Fin j → Covariate d) × partitionFieldMark (Covariate d × ℝ) =>
      ∏ l, boundedHyperplaneFieldValue Uz.2 (Uz.1 l)) :=
    Finset.measurable_prod _ (fun l _ =>
      (boundedHyperplaneFieldValue_measurable d).comp
        (measurable_snd.prodMk ((measurable_pi_apply l).comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem boundedHyperplaneSpatialMoment_abs_le_one (d : ℕ) [NeZero d]
    (T : ℝ) (j : ℕ) (U : Fin j → Covariate d) :
    |boundedHyperplaneSpatialMoment d T j U| ≤ 1 := by
  unfold boundedHyperplaneSpatialMoment
  calc
    _ ≤ ∫ z, |∏ l, boundedHyperplaneFieldValue z (U l)| ∂boundedHyperplaneFieldLaw d T :=
      abs_integral_le_integral_abs
    _ = 1 := by simp only [Finset.abs_prod, boundedHyperplaneFieldValue_abs,
      Finset.prod_const_one, integral_const, probReal_univ, smul_eq_mul, one_mul]

def spatialQuadDistance {d j : ℕ} (q : CellMomentQuadruple j)
    (U : Fin j → Covariate d) : ℝ :=
  exactEuclideanDistance (U (q.val 0)) (U (q.val 1)) +
    exactEuclideanDistance (U (q.val 2)) (U (q.val 3))

theorem spatialQuadDistance_nonneg {d j : ℕ} (q : CellMomentQuadruple j)
    (U : Fin j → Covariate d) : 0 ≤ spatialQuadDistance q U :=
  add_nonneg (exactEuclideanDistance_nonneg _ _) (exactEuclideanDistance_nonneg _ _)

theorem spatialQuadDistance_continuous {d j : ℕ} (q : CellMomentQuadruple j) :
    Continuous (spatialQuadDistance (d := d) q) := by
  have hm01 : Continuous (fun U : Fin j → Covariate d => (U (q.val 0), U (q.val 1))) :=
    (continuous_apply (q.val 0)).prodMk (continuous_apply (q.val 1))
  have hm23 : Continuous (fun U : Fin j → Covariate d => (U (q.val 2), U (q.val 3))) :=
    (continuous_apply (q.val 2)).prodMk (continuous_apply (q.val 3))
  have h01 : Continuous (fun U : Fin j → Covariate d =>
      exactEuclideanDistance (U (q.val 0)) (U (q.val 1))) := by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous (d := d)).comp hm01
  have h23 : Continuous (fun U : Fin j → Covariate d =>
      exactEuclideanDistance (U (q.val 2)) (U (q.val 3))) := by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous (d := d)).comp hm23
  exact h01.add h23

theorem spatialPatchBox_eq_hyperplaneCube (d : ℕ) :
    spatialPatchBox d = hyperplaneCube d := by
  ext x
  simp only [spatialPatchBox, mem_Icc, Pi.le_def, hyperplaneCube, mem_ofPred_eq, abs_le]
  exact ⟨fun h r => ⟨h.1 r, h.2 r⟩, fun h => ⟨fun r => (h r).1, fun r => (h r).2⟩⟩

theorem spatialPatchProbability_ae_cube (d : ℕ) :
    ∀ᵐ x ∂spatialPatchProbability d, x ∈ hyperplaneCube d := by
  rw [spatialPatchProbability, ← spatialPatchBox_eq_hyperplaneCube]
  exact (ae_restrict_mem measurableSet_Icc).filter_mono (Measure.ae_smul_measure_le _)

/-- The true independent local-cube law has every coordinate in the source cube almost surely. -/
theorem spatialPatchProbability_pi_ae_cube (d j : ℕ) :
    ∀ᵐ U ∂Measure.pi (fun _ : Fin j => spatialPatchProbability d),
      ∀ l, U l ∈ hyperplaneCube d := by
  apply ae_all_iff.mpr
  intro l
  exact (measurePreserving_eval (fun _ : Fin j => spatialPatchProbability d) l).quasiMeasurePreserving.tendsto_ae.eventually
    (spatialPatchProbability_ae_cube d)

/-- Genuine squared higher-moment bound under normalized independent spatial coordinates. -/
theorem boundedHyperplaneSpatialMoment_squared_probability_integral_le
    (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 < T) (j : ℕ) (hj : 4 ≤ j) :
    (∫ U : Fin j → Covariate d, (boundedHyperplaneSpatialMoment d T j U)^2
      ∂Measure.pi (fun _ : Fin j => spatialPatchProbability d)) ≤
      (j : ℝ)^8 * (spatialExponentialConstant d / T^d)^2 := by
  classical
  let π := spatialPatchProbability d
  let μ := Measure.pi (fun _ : Fin j => π)
  let a : ℝ := Fintype.card (CellMomentQuadruple j)
  let E : CellMomentQuadruple j → (Fin j → Covariate d) → ℝ :=
    fun q U => Real.exp (-(T * spatialQuadDistance q U))
  have hem (q : CellMomentQuadruple j) : Measurable (E q) :=
    (spatialQuadDistance_continuous q |>.const_mul T |>.neg |>.rexp).measurable
  have hei (q : CellMomentQuadruple j) : Integrable (E q) μ :=
    Integrable.of_bound (hem q).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (spatialQuadDistance_nonneg q U))))
  have hmi : Integrable (fun U => (boundedHyperplaneSpatialMoment d T j U)^2) μ :=
    Integrable.of_bound ((boundedHyperplaneSpatialMoment_measurable d T j).pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [boundedHyperplaneSpatialMoment_abs_le_one d T j U, abs_nonneg (boundedHyperplaneSpatialMoment d T j U),
          sq_abs (boundedHyperplaneSpatialMoment d T j U)])
  have hpoint : ∀ᵐ U ∂μ, (boundedHyperplaneSpatialMoment d T j U)^2 ≤ a * ∑ q, E q U := by
    filter_upwards [spatialPatchProbability_pi_ae_cube d j] with U hU
    have hb := boundedHyperplaneField_higher_moment_envelope d T hT.le j hj U hU
    simp_rw [← exactEuclideanDistance_eq_euclideanNorm] at hb
    change |boundedHyperplaneSpatialMoment d T j U| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * spatialQuadDistance q U) at hb
    have hsum : 0 ≤ ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * spatialQuadDistance q U) :=
      Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun q : CellMomentQuadruple j => Real.exp (-T / 2 * spatialQuadDistance q U))
    have hsq : (boundedHyperplaneSpatialMoment d T j U)^2 ≤
        (∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * spatialQuadDistance q U))^2 := by
      nlinarith [sq_abs (boundedHyperplaneSpatialMoment d T j U), abs_nonneg (boundedHyperplaneSpatialMoment d T j U)]
    have heq (q : CellMomentQuadruple j) :
        Real.exp (-T / 2 * spatialQuadDistance q U)^2 = E q U := by
      rw [← Real.exp_nat_mul]
      apply congrArg Real.exp
      dsimp [E]
      ring
    exact hsq.trans (by simpa only [Finset.card_univ, heq, a] using hs)
  have hpair (q : CellMomentQuadruple j) : (∫ U, E q U ∂μ) ≤ (spatialExponentialConstant d / T^d)^2 := by
    rw [show (∫ U, E q U ∂μ) =
        (∫ xy : Covariate d × Covariate d, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 from
      spatialPi_two_pairs_integral_factor π ⟨q.val,q.property⟩ T]
    have hb := spatial_probability_pair_exponential_integral_le (NeZero.pos d) π (spatialPatchProbability_le_volume d) hT
    have h0 : 0 ≤ ∫ xy : Covariate d × Covariate d, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂π.prod π :=
      integral_nonneg (fun _ => (Real.exp_pos _).le)
    nlinarith
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hac : a ≤ (j : ℝ)^4 := by
    dsimp [a]
    exact_mod_cast cellMomentQuadruple_card_le j
  calc
    _ ≤ ∫ U, a * ∑ q, E q U ∂μ :=
      integral_mono_ae hmi ((integrable_finsetSum _ (fun q _ => hei q)).const_mul a) hpoint
    _ = a * ∑ q, ∫ U, E q U ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun q _ => hei q)]
    _ ≤ a * ∑ _q : CellMomentQuadruple j, (spatialExponentialConstant d / T^d)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hpair q)) ha
    _ = a^2 * (spatialExponentialConstant d / T^d)^2 := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, a]; ring
    _ ≤ _ := by
      have hb : a^2 ≤ (j : ℝ)^8 := by
        simpa only [← pow_mul] using pow_le_pow_left₀ ha hac 2
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

/-- The actual source cube volume is its volume times the genuine uniform law. -/
theorem spatialPatchVolume_eq_smulProbability (d : ℕ) :
    volume.restrict (spatialPatchBox d) = (2 : ℝ≥0∞)^d • spatialPatchProbability d := by
  rw [spatialPatchProbability, smul_smul, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_smul]

/-- The actual squared field moment is genuinely integrable on every finite spatial cube product. -/
theorem boundedHyperplaneSpatialMoment_squared_cube_integrable
    (d : ℕ) [NeZero d] (T : ℝ) (j : ℕ) :
    Integrable (fun U : Fin j → Covariate d => (boundedHyperplaneSpatialMoment d T j U)^2)
      (Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d))) := by
  apply Integrable.of_bound ((boundedHyperplaneSpatialMoment_measurable d T j).pow_const 2).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro U
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [boundedHyperplaneSpatialMoment_abs_le_one d T j U,
    abs_nonneg (boundedHyperplaneSpatialMoment d T j U), sq_abs (boundedHyperplaneSpatialMoment d T j U)]

/-- The genuine unnormalized source-cube product integral with the exact volume factor. -/
theorem boundedHyperplaneSpatialMoment_squared_cube_integral_le
    (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 < T) (j : ℕ) (hj : 4 ≤ j) :
    (∫ U : Fin j → Covariate d, (boundedHyperplaneSpatialMoment d T j U)^2
      ∂Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d))) ≤
      (2 : ℝ)^(d*j) * (j : ℝ)^8 * (spatialExponentialConstant d / T^d)^2 := by
  let : IsFiniteMeasure ((2 : ℝ≥0∞)^d • spatialPatchProbability d) := by
    rw [← spatialPatchVolume_eq_smulProbability]
    infer_instance
  have he : Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d)) =
      ((2 : ℝ≥0∞)^d)^j • Measure.pi (fun _ : Fin j => spatialPatchProbability d) := by
    simp only [spatialPatchVolume_eq_smulProbability]
    simpa only [Fintype.card_fin] using spatialPi_const_smul (J := Fin j) (spatialPatchProbability d) ((2 : ℝ≥0∞)^d)
  rw [he, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, smul_eq_mul, ← pow_mul]
  have hb := boundedHyperplaneSpatialMoment_squared_probability_integral_le d T hT j hj
  convert mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2 : ℝ)^(d*j)) using 1; ring

/-- A fixed dimension constant for the actual higher-moment spatial L² estimate. -/
def hyperplaneSpatialMomentConstant (d : ℕ) : ℝ :=
  (2 : ℝ)^d * (1 + spatialExponentialConstant d)

theorem hyperplaneSpatialMomentConstant_positive (d : ℕ) :
    0 < hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have := spatialExponentialConstant_nonneg d
  positivity

/-- The paper's higher-moment L² estimate for the genuinely constructed field,
with no spatial-moment or integral bound as a premise. -/
theorem boundedHyperplaneSpatialMoment_L2_le
    (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 < T) (j : ℕ) (hj : 4 ≤ j) :
    Real.sqrt (∫ U : Fin j → Covariate d, (boundedHyperplaneSpatialMoment d T j U)^2
      ∂Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d))) ≤
      (hyperplaneSpatialMomentConstant d)^j * (j : ℝ)^4 / T^d := by
  let C := spatialExponentialConstant d
  have hC : 0 ≤ C := spatialExponentialConstant_nonneg d
  have h2 : 1 ≤ (2 : ℝ)^d := one_le_pow₀ (by norm_num)
  have hC1 : 1 ≤ 1+C := by linarith
  have hV : (2 : ℝ)^(d*j) ≤ ((2 : ℝ)^d)^(2*j) := by
    rw [pow_mul]
    exact pow_le_pow_right₀ h2 (by omega)
  have hCp : C^2 ≤ (1+C)^(2*j) := by
    calc C^2 ≤ (1+C)^2 := pow_le_pow_left₀ hC (by linarith) 2
         _ ≤ _ := pow_le_pow_right₀ hC1 (by omega)
  have hconstant : (2 : ℝ)^(d*j) * C^2 ≤ (hyperplaneSpatialMomentConstant d)^(2*j) := by
    unfold hyperplaneSpatialMomentConstant
    rw [mul_pow]
    exact mul_le_mul hV hCp (sq_nonneg C) (by positivity)
  have hb := boundedHyperplaneSpatialMoment_squared_cube_integral_le d T hT j hj
  have hupper : (2 : ℝ)^(d*j) * (j : ℝ)^8 * (C/T^d)^2 ≤
      ((hyperplaneSpatialMomentConstant d)^j * (j : ℝ)^4 / T^d)^2 := by
    have ht := mul_le_mul_of_nonneg_right hconstant (show 0 ≤ (j : ℝ)^8 / (T^d)^2 by positivity)
    convert ht using 1 <;> simp only [div_pow, mul_pow, ← pow_mul] <;> ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity [hyperplaneSpatialMomentConstant_positive d], hb.trans hupper⟩

end NearlyMinimax
