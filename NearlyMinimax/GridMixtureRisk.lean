module

public import NearlyMinimax.LowMixtureLaw
public import NearlyMinimax.LowMixtureProbability
public import NearlyMinimax.GridMixtureDerivative
public import NearlyMinimax.GridScorePath


@[expose] public section

/-! Genuine original-model prior risk and centered score bounds for the grid experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem gridSampleField_coordinate_measurable (d k n : ℕ) (η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
    Measurable (fun x => gridSampleField d k n η x ξ i) :=
  (measurable_pi_apply i).comp ((measurable_pi_apply ξ).comp
    (gridSampleField_measurable d k n η))

def gridMixtureLaw (d k n : ℕ) (a v η t : ℝ) :
    Measure ((Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n) :=
  lowMixtureLaw (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n
    a (v - η ^ 2 * t) t (gridSampleField d k n η)
    (gridSampleField_coordinate_measurable d k n η)

def gridMixtureScore (d k n : ℕ) (a v η t : ℝ) :
    (Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  lowMixtureScore (gridWindowCount d k) n a (v - η ^ 2 * t) η (gridSampleField d k n η)

def gridLiftedObservable {d n : ℕ} (k : ℕ) (a : ℝ) (T : Estimator d n) :
    (Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  fun z => T.val (encodeDesignResponse a (z.1, z.2.2))

theorem gridLiftedObservable_measurable {d n : ℕ} (k : ℕ) (a : ℝ)
    (T : Estimator d n) : Measurable (gridLiftedObservable k a T) :=
  (T.property.comp (encodeDesignResponse_measurable a)).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

theorem gridSampleField_eq_latent (d k n : ℕ) (η : ℝ) (x : Fin n → Covariate d) :
    gridSampleField d k n η x =
      latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) := by
  funext ξ i
  exact (grid_latent_regression_eq d k n η x ξ i).symm

theorem gridMixtureConditionalEnergy_integrable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    Integrable (lowMixtureConditionalScoreEnergy (gridWindowCount d k) n P.a
      (P.v - η ^ 2 * t) η t (gridSampleField d k n η))
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  unfold lowMixtureConditionalScoreEnergy
  have hξ (ξ : Fin (gridWindowCount d k) → Fin 3) :=
    (grid_full_score_energy_integrable C P k n η t ξ hη ht hfield hvariance).const_mul
      (activationProductPrior (gridWindowCount d k) t ξ)
  dsimp only [gridFullScoreEnergy] at hξ
  simpa only [gridFullScoreEnergy,
    LowSmoothnessTernaryConstants.variancePath, gridSampleField_eq_latent] using
    integrable_finsetSum (Finset.univ : Finset (Fin (gridWindowCount d k) → Fin 3)) (fun ξ _ => hξ ξ)

theorem grid_mixture_probability {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    IsProbabilityMeasure (gridMixtureLaw d k n P.a P.v η t) := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureLaw_probability _ _ _ _ _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)

theorem grid_mixture_score_memLp {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    MemLp (gridMixtureScore d k n P.a P.v η t) 2
      (gridMixtureLaw d k n P.a P.v η t) := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureScore_memLp_two _ _ _ _ _ _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)
    (gridMixtureConditionalEnergy_integrable C P k n η t hη ht hfield hvariance)

theorem grid_mixture_score_centered {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    (∫ z, gridMixtureScore d k n P.a P.v η t z
      ∂gridMixtureLaw d k n P.a P.v η t) = 0 := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureScore_centered _ _ _ _ _ _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y)
    (gridMixtureConditionalEnergy_integrable C P k n η t hη ht hfield hvariance)

theorem grid_mixture_score_energy {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    (∫ z, (gridMixtureScore d k n P.a P.v η t z) ^ 2
      ∂gridMixtureLaw d k n P.a P.v η t) = gridPriorScoreEnergy d k n P.a P.v η t := by
  let _ := cubeVolume_isProbability d
  have hξ (ξ : Fin (gridWindowCount d k) → Fin 3) :=
    grid_full_score_energy_integrable C P k n η t ξ hη ht hfield hvariance
  simpa only [gridMixtureScore, gridMixtureLaw, gridPriorScoreEnergy,
    gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath,
    gridSampleField_eq_latent] using lowMixtureScore_sq_integral_eq_sum
      (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n
      P.a (P.v - η ^ 2 * t) η t (gridSampleField d k n η)
      (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
      (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)
      (fun ξ => (hξ ξ).congr (Filter.Eventually.of_forall (fun x => by
        simp only [gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath,
          gridSampleField_eq_latent])))

theorem grid_lifted_observable_memLp {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : BoundedEstimator C n) :
    MemLp (gridLiftedObservable k P.a T.val) 2 (gridMixtureLaw d k n P.a P.v η t) := by
  let _ := grid_mixture_probability C P k n η t hη ht hfield hvariance
  apply MemLp.of_bound (gridLiftedObservable_measurable k P.a T.val).aestronglyMeasurable
    (effectiveVarianceUpper C)
  apply Filter.Eventually.of_forall
  intro z
  change |T.val.val (encodeDesignResponse P.a (z.1, z.2.2))| ≤ effectiveVarianceUpper C
  rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property _).1)]
  exact (T.property _).2

def gridStateRisk {d n : ℕ} (k : ℕ) (a v η t : ℝ) (T : Estimator d n)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d) : ℝ :=
  ∑ y : Fin n → Fin 3, finiteResponseLikelihood (gridWindowCount d k) n a
    (v - η ^ 2 * t) (gridSampleField d k n η x) ξ y *
      (T.val (encodeDesignResponse a (x, y)) - (v - η ^ 2 * t)) ^ 2

theorem grid_state_risk_integrable {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : BoundedEstimator C n) (ξ : Fin (gridWindowCount d k) → Fin 3) :
    Integrable (gridStateRisk k P.a P.v η t T.val ξ)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  let V := P.v - η ^ 2 * t
  let B := (effectiveVarianceUpper C + |V|) ^ 2
  have hp (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
      0 ≤ finiteResponseLikelihood (gridWindowCount d k) n P.a V
        (gridSampleField d k n η x) ξ y :=
    (grid_response_likelihood_pos C P k n η t hη ht hfield hvariance x ξ y).le
  have hb (z : Fin n → Observation d) : (T.val.val z - V) ^ 2 ≤ B := by
    have hab : |T.val.val z| ≤ effectiveVarianceUpper C := by
      rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
      exact (T.property z).2
    have he := (abs_sub (T.val.val z) V).trans (add_le_add hab (le_refl |V|))
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he 2
  have hm : Measurable (gridStateRisk k P.a P.v η t T.val ξ) := by
    apply Finset.measurable_sum
    intro y _
    exact (finiteResponseLikelihood_measurable_comp _ _ _ _ _
      (gridSampleField_coordinate_measurable d k n η) ξ y).mul
      (((T.val.property.comp (encodeDesignResponse_measurable P.a)).comp
        (measurable_id.prodMk measurable_const)).sub_const V |>.pow_const 2)
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hnn : 0 ≤ gridStateRisk k P.a P.v η t T.val ξ x :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hp x y) (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc
    _ ≤ ∑ y : Fin n → Fin 3, finiteResponseLikelihood (gridWindowCount d k) n P.a V
      (gridSampleField d k n η x) ξ y * B :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hb _) (hp x y))
    _ = B := by
      rw [← Finset.sum_mul, finite_response_normalized _ _ _ _ _ _ P.a_pos.ne', one_mul]

theorem grid_mixture_risk_le_original_worstCase {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b t : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound)
    (T : BoundedEstimator C n) :
    (∫ z, (gridLiftedObservable k P.a T.val z - (P.v - η ^ 2 * t)) ^ 2
      ∂gridMixtureLaw d k n P.a P.v η t) ≤ (worstCaseRisk C T.val).toReal := by
  let _ := cubeVolume_isProbability d
  have hξ (ξ : Fin (gridWindowCount d k) → Fin 3) :=
    grid_state_risk_integrable C P k η t hη ht hfield hvariance T ξ
  unfold gridMixtureLaw
  rw [lowMixtureLaw_nonneg_integral_sum
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n
    P.a (P.v - η ^ 2 * t) t (gridSampleField d k n η)
    (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)
    _ ((gridLiftedObservable_measurable k P.a T.val).sub_const _ |>.pow_const 2)
    (fun _ => sq_nonneg _) hξ]
  calc
    _ ≤ ∑ ξ : Fin (gridWindowCount d k) → Fin 3,
      activationProductPrior (gridWindowCount d k) t ξ * (worstCaseRisk C T.val).toReal := by
      apply Finset.sum_le_sum
      intro ξ _
      apply mul_le_mul_of_nonneg_left
      · apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top C T)).mp
        exact gridPathParameter_finite_risk_le_worstCase C P k η b t ξ hk hs1 hb hη ht
          hfield hvariance hscale hholder T
      · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative t ht.1 ht.2 (ξ j))
    _ = _ := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]

def gridEncodedObservable {d n : ℕ} (a : ℝ) (T : Estimator d n) :
    (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ :=
  fun x y => T.val (encodeDesignResponse a (x, y))

theorem gridEncodedObservable_measurable {d n : ℕ} (a : ℝ) (T : Estimator d n) :
    Measurable (gridEncodedObservable a T) := by
  apply Measurable.of_eval
  intro y
  exact (T.property.comp (encodeDesignResponse_measurable a)).comp
    (measurable_id.prodMk measurable_const)

theorem gridEncodedObservable_norm_le {d n : ℕ} (C : ModelConstants d)
    (a : ℝ) (T : BoundedEstimator C n) (x : Fin n → Covariate d) :
    ‖gridEncodedObservable a T.val x‖ ≤ effectiveVarianceUpper C := by
  have hC : 0 ≤ effectiveVarianceUpper C :=
    C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro y
  change |T.val.val (encodeDesignResponse a (x, y))| ≤ effectiveVarianceUpper C
  rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property _).1)]
  exact (T.property _).2

theorem grid_mixture_mean_eq {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : BoundedEstimator C n) :
    (∫ z, gridLiftedObservable k P.a T.val z ∂gridMixtureLaw d k n P.a P.v η t) =
      gridMixtureExpectation d k n P.a P.v η t (gridEncodedObservable P.a T.val) := by
  let _ := cubeVolume_isProbability d
  let _ := grid_mixture_probability C P k n η t hη ht hfield hvariance
  have hi := (grid_lifted_observable_memLp C P k η t hη ht hfield hvariance T).integrable
    (by norm_num)
  exact lowMixtureLaw_integral (Measure.pi (fun _ : Fin n => cubeVolume d))
    (gridWindowCount d k) n P.a (P.v - η ^ 2 * t) t (gridSampleField d k n η)
    (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le) _ hi

theorem grid_mixture_score_observable_eq {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : BoundedEstimator C n) :
    (∫ z, gridLiftedObservable k P.a T.val z * gridMixtureScore d k n P.a P.v η t z
      ∂gridMixtureLaw d k n P.a P.v η t) =
      ∫ x, gridMixtureScoreObservable d k n P.a P.v η t (gridEncodedObservable P.a T.val) x
        ∂Measure.pi (fun _ : Fin n => cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  have hi := (grid_lifted_observable_memLp C P k η t hη ht hfield hvariance T).integrable_mul
    (grid_mixture_score_memLp C P k n η t hη ht hfield hvariance)
  simpa only [gridLiftedObservable, gridMixtureScore, gridMixtureLaw,
    gridMixtureScoreObservable, gridEncodedObservable, lowMixtureScore, Pi.mul_apply, mul_assoc,
    LowSmoothnessTernaryConstants.variancePath, gridSampleField] using
    lowMixtureLaw_integral (Measure.pi (fun _ : Fin n => cubeVolume d))
      (gridWindowCount d k) n P.a (P.v - η ^ 2 * t) t (gridSampleField d k n η)
      (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
      (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le) _ hi

/-- The complete actual-model score argument. All latent states obey the
original Hölder/moment class and all score and risk identities are derived. -/
theorem grid_prior_boundedEstimator_separation {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) (hbudget : gridUniformScoreBudget P k n η ≤ 1)
    (T : BoundedEstimator C n) :
    η ^ 2 ≤ 3 * Real.sqrt ((worstCaseRisk C T.val).toReal) := by
  let r := Real.sqrt ((worstCaseRisk C T.val).toReal)
  let m := fun t => gridMixtureExpectation d k n P.a P.v η t (gridEncodedObservable P.a T.val)
  let m' := fun t => ∫ x,
    gridMixtureScoreObservable d k n P.a P.v η t (gridEncodedObservable P.a T.val) x
    ∂Measure.pi (fun _ : Fin n => cubeVolume d)
  let sn := fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (worstCaseRisk C T.val).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hT := gridEncodedObservable_measurable P.a T.val
  have hTB : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d),
      ‖gridEncodedObservable P.a T.val x‖ ≤ effectiveVarianceUpper C :=
    Filter.Eventually.of_forall (gridEncodedObservable_norm_le C P.a T)
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt m (m' t) t :=
    (grid_mixture_expectation_hasDerivAt C P k n η t (effectiveVarianceUpper C)
      hη ht hfield hvariance _ hT hTB).2
  have hderivI : IntervalIntegrable m' volume 0 1 :=
    grid_mixture_score_observable_intervalIntegrable C P k n η (effectiveVarianceUpper C)
      hη hfield hvariance _ hT hTB
  have hscoreI : IntervalIntegrable sn volume 0 1 :=
    grid_sqrt_score_energy_intervalIntegrable C P k n η hk hη hfield hvariance hmean
  have hris (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ z, (gridLiftedObservable k P.a T.val z - (P.v - η ^ 2 * t)) ^ 2
        ∂gridMixtureLaw d k n P.a P.v η t) ≤ r ^ 2 := by
    rw [hr2]
    exact grid_mixture_risk_le_original_worstCase C P k η b t hk hs1 hb hη ht
      hfield hvariance hscale hholder T
  have hderivBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |m' t| ≤ r * sn t := by
    let _ := grid_mixture_probability C P k n η t hη ht hfield hvariance
    have h := probability_score_bound (gridMixtureLaw d k n P.a P.v η t)
      (gridLiftedObservable k P.a T.val) (gridMixtureScore d k n P.a P.v η t)
      (P.v - η ^ 2 * t) r
      (grid_lifted_observable_memLp C P k η t hη ht hfield hvariance T)
      (grid_mixture_score_memLp C P k n η t hη ht hfield hvariance) hr
      (grid_mixture_score_centered C P k n η t hη ht hfield hvariance) (hris t ht)
    rw [grid_mixture_score_observable_eq C P k η t hη ht hfield hvariance T,
      grid_mixture_score_energy C P k n η t hη ht hfield hvariance] at h
    exact h
  have hbias (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |m t - (P.v - η ^ 2 * t)| ≤ r := by
    let _ := grid_mixture_probability C P k n η t hη ht hfield hvariance
    have h := probability_mean_error_le (gridMixtureLaw d k n P.a P.v η t)
      (gridLiftedObservable k P.a T.val) (P.v - η ^ 2 * t) r
      (grid_lifted_observable_memLp C P k η t hη ht hfield hvariance T) hr (hris t ht)
    rw [grid_mixture_mean_eq C P k η t hη ht hfield hvariance T] at h
    exact h
  have hsep := path_separation_le (by norm_num : (0 : ℝ) ≤ 1) hderiv hderivI hscoreI
    hderivBound (hbias 0 (by norm_num)) (hbias 1 (by norm_num))
  have hscoreBudget := grid_sqrt_score_energy_integral_le_one C P k n η hk hη hfield
    hvariance hmean hbudget
  have he : |(P.v - η ^ 2 * 1) - (P.v - η ^ 2 * 0)| = η ^ 2 := by
    simp [abs_of_nonneg (sq_nonneg η)]
  rw [he] at hsep
  exact hsep.trans (mul_le_mul_of_nonneg_right (by linarith) hr)

/-- Actual minimax RMS lower bound from the fully constructed grid prior. -/
theorem grid_prior_minimax_lower {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) (hbudget : gridUniformScoreBudget P k n η ≤ 1) :
    ENNReal.ofReal (η ^ 2 / 3) ≤ minimaxRMS C n := by
  have hnonneg : 0 ≤ η ^ 2 / 3 := by positivity
  have hlower : ENNReal.ofReal (η ^ 2 / 3) ^ 2 ≤ minimaxRisk C n := by
    rw [minimaxRisk_eq_inf_bounded C n]
    apply le_iInf
    intro T
    rw [← ENNReal.ofReal_pow hnonneg 2]
    apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top C T)).mpr
    have hsep := grid_prior_boundedEstimator_separation C P k η b hk hs1 hb hη
      hfield hvariance hscale hholder hmean hbudget T
    have hdiv : η ^ 2 / 3 ≤ Real.sqrt ((worstCaseRisk C T.val).toReal) := by linarith
    have hsq := pow_le_pow_left₀ hnonneg hdiv 2
    rwa [Real.sq_sqrt ENNReal.toReal_nonneg] at hsq
  have h := ENNReal.rpow_le_rpow hlower (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : (ENNReal.ofReal (η ^ 2 / 3) ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (η ^ 2 / 3) := by
    rw [← ENNReal.rpow_natCast_mul]
    norm_num
  rw [he] at h
  exact h

end NearlyMinimax
