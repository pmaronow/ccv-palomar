module

public import NearlyMinimax.GridMixtureDerivative


@[expose] public section

/-! Measurability and integrated square-root score budget for the actual grid path. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators
namespace NearlyMinimax

theorem grid_full_score_energy_joint_measurable (d k n : ℕ) (a v η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) :
    Measurable (fun z : ℝ × (Fin n → Covariate d) =>
      gridFullScoreEnergy d k n a (v - η ^ 2 * z.1) η ξ z.2) := by
  let f : (ℝ × (Fin n → Covariate d)) →
      (Fin (gridWindowCount d k) → Fin 3) → Fin n → ℝ :=
    fun z => latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n z.2)
  have hV : Measurable (fun z : ℝ × (Fin n → Covariate d) => v - η ^ 2 * z.1) := by fun_prop
  have hf (ξ' : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
      Measurable (fun z => f z ξ' i) := by
    have hDesign : Measurable (fun z : ℝ × (Fin n → Covariate d) => z.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    have hComp := (indexedGridField_continuous d k η ξ').measurable.comp hDesign
    simpa only [f, grid_latent_regression_eq, Function.comp_def] using hComp
  have hq (ξ' : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) (y : Fin 3) :
      Measurable (fun z => ternaryMass a (f z ξ' i) (v - η ^ 2 * z.1) y) := by
    have hPair := (hf ξ' i).prodMk hV
    have hComp := (ternaryMass_joint_continuous a y).measurable.comp hPair
    exact hComp
  have hL (ξ' : Fin (gridWindowCount d k) → Fin 3) (y : Fin n → Fin 3) :
      Measurable (fun z => finiteResponseLikelihood (gridWindowCount d k) n a
        (v - η ^ 2 * z.1) (f z) ξ' y) :=
    Finset.measurable_prod _ (fun i _ => hq ξ' i (y i))
  have hU (y : Fin n → Fin 3) (i : Fin n) :
      Measurable (fun z => finiteResponseVarianceTerm (gridWindowCount d k) n a
        (v - η ^ 2 * z.1) (f z) ξ y i) :=
    (Finset.measurable_prod _ (fun l _ => hq ξ l (y l))).const_mul _
  have hD (y : Fin n → Fin 3) (j : Fin (gridWindowCount d k)) :
      Measurable (fun z => latentDifference (gridWindowCount d k) j
        (fun ξ' => finiteResponseLikelihood (gridWindowCount d k) n a
          (v - η ^ 2 * z.1) (f z) ξ' y) ξ) :=
    (((hL (Function.update ξ j 2) y).const_mul (1 / 2)).add
      ((hL (Function.update ξ j 0) y).const_mul (1 / 2))).sub (hL (Function.update ξ j 1) y)
  have hR (y : Fin n → Fin 3) :
      Measurable (fun z => finiteExperimentScore (gridWindowCount d k) n a
        (v - η ^ 2 * z.1) η (f z) ξ y) :=
    ((Finset.measurable_sum _ (fun j _ => hD y j)).sub
      ((Finset.measurable_sum _ (fun i _ => hU y i)).const_mul (η ^ 2))).div (hL ξ y)
  exact Finset.measurable_sum _ (fun y _ => (hL ξ y).mul ((hR y).pow_const 2))

theorem grid_prior_score_energy_path_measurable (d k n : ℕ) (a v η : ℝ) :
    Measurable (gridPriorScoreEnergy d k n a v η) := by
  let _ := cubeVolume_isProbability d
  unfold gridPriorScoreEnergy
  apply Finset.measurable_sum
  intro ξ _
  have hPrior : Measurable (fun t => activationProductPrior (gridWindowCount d k) t ξ) :=
    (continuous_iff_continuousAt.mpr (fun t =>
      (activation_product_prior_hasDerivAt (gridWindowCount d k) t ξ).continuousAt)).measurable
  have hInt := (grid_full_score_energy_joint_measurable d k n a v η ξ).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi (fun _ : Fin n => cubeVolume d))
  exact hPrior.mul hInt.measurable

def gridUniformScoreBudget {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) : ℝ :=
  (40 : ℝ) ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
    Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * n ^ 2 * η ^ 4 / (k : ℝ) ^ d

theorem grid_sqrt_score_energy_intervalIntegrable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) (hk : 1 ≤ k)
    (hη : 0 ≤ η) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    IntervalIntegrable (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) volume 0 1 := by
  have hMeas : Measurable (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) :=
    Real.continuous_sqrt.measurable.comp (grid_prior_score_energy_path_measurable d k n P.a P.v η)
  have hI : IntegrableOn (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) (Icc 0 1) volume := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable (Real.sqrt (gridUniformScoreBudget P k n η))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (grid_prior_score_energy_bound C P k n η t hk hη ht hfield hvariance hmean)
  apply IntegrableOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hI

theorem grid_sqrt_score_energy_integral_le {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) (hk : 1 ≤ k)
    (hη : 0 ≤ η) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    (∫ t in (0 : ℝ)..1, Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) ≤
      Real.sqrt (gridUniformScoreBudget P k n η) := by
  have hInt := grid_sqrt_score_energy_intervalIntegrable C P k n η hk hη hfield hvariance hmean
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hInt
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.sqrt (gridUniformScoreBudget P k n η)) volume 0 1)
    (fun t ht => Real.sqrt_le_sqrt (grid_prior_score_energy_bound C P k n η t hk hη ht hfield hvariance hmean))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

theorem grid_sqrt_score_energy_integral_le_one {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) (hk : 1 ≤ k)
    (hη : 0 ≤ η) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) (hbudget : gridUniformScoreBudget P k n η ≤ 1) :
    (∫ t in (0 : ℝ)..1, Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) ≤ 1 := by
  apply (grid_sqrt_score_energy_integral_le C P k n η hk hη hfield hvariance hmean).trans
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hbudget

end NearlyMinimax
