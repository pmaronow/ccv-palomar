module

public import NearlyMinimax.LowMixtureDerivative
public import NearlyMinimax.LowSmoothnessGridExperiment


@[expose] public section

/-! The design-integrated derivative for the paper's actual grid prior. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators
namespace NearlyMinimax

def gridSampleField (d k n : ℕ) (η : ℝ) (x : Fin n → Covariate d) :
    (Fin (gridWindowCount d k) → Fin 3) → Fin n → ℝ :=
  fun ξ i => indexedGridField d k η ξ (x i)

theorem gridSampleField_measurable (d k n : ℕ) (η : ℝ) :
    Measurable (gridSampleField d k n η) := by
  apply measurable_pi_lambda
  intro ξ
  apply measurable_pi_lambda
  intro i
  have h := (indexedGridField_continuous d k η ξ).measurable.comp
    (show Measurable (fun x : Fin n → Covariate d => x i) from measurable_pi_apply i)
  exact h

theorem gridSampleField_norm_le (d k n : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (x : Fin n → Covariate d) : ‖gridSampleField d k n η x‖ ≤ (2 : ℝ) ^ d * η := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simpa only [gridSampleField, Real.norm_eq_abs] using indexedGridField_abs_bound d k η hη ξ (x i)

def gridMixtureExpectation (d k n : ℕ) (a v η t : ℝ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) : ℝ :=
  ∫ x, finiteExperimentExpectation (gridWindowCount d k) n a v η t
    (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _ : Fin n => cubeVolume d)

def gridMixtureScoreObservable (d k n : ℕ) (a v η t : ℝ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (x : Fin n → Covariate d) : ℝ :=
  ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ * ∑ y,
    finiteResponseLikelihood (gridWindowCount d k) n a (v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y * T x y *
    finiteExperimentScore (gridWindowCount d k) n a (v - η ^ 2 * t) η
      (gridSampleField d k n η x) ξ y

theorem grid_response_likelihood_pos {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (x : Fin n → Covariate d) (ξ : Fin (gridWindowCount d k) → Fin 3) (y : Fin n → Fin 3) :
    0 < finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y := by
  have hBase : (2 : ℝ) ^ d * η ≤ P.ρ := by nlinarith
  unfold finiteResponseLikelihood
  apply Finset.prod_pos
  intro i _
  have hAbs : |indexedGridField d k η ξ (x i)| ≤ P.ρ :=
    (indexedGridField_abs_bound d k η hη ξ (x i)).trans hBase
  exact P.c_pos.trans_le ((P.path_legality η t _ ht hvariance hAbs).2.2.1 (y i))

/-- The actual grid-prior mean has the exact integrated score derivative.
Every domination, measurability, and positivity requirement follows from
the grid construction and the original ternary legality neighborhood. -/
theorem grid_mixture_expectation_hasDerivAt {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t M : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d), ‖T x‖ ≤ M) :
    Integrable (gridMixtureScoreObservable d k n P.a P.v η t T)
        (Measure.pi (fun _ : Fin n => cubeVolume d)) ∧
      HasDerivAt (fun u => gridMixtureExpectation d k n P.a P.v η u T)
        (∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
          ∂Measure.pi (fun _ : Fin n => cubeVolume d)) t := by
  let _ := cubeVolume_isProbability d
  have hp : ∀ (x : Fin n → Covariate d) ξ y,
      0 < finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
        (gridSampleField d k n η x) ξ y := by
    exact grid_response_likelihood_pos C P k n η t hη ht hfield hvariance
  exact finite_experiment_integrated_score_hasDerivAt
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n P.a P.v η t
    ((2 : ℝ) ^ d * η) M (gridSampleField d k n η) T
    (gridSampleField_measurable d k n η) hT
    (Filter.Eventually.of_forall (gridSampleField_norm_le d k n η hη)) hTBound
    (Filter.Eventually.of_forall hp)

theorem grid_mixture_raw_derivative_continuous (d k n : ℕ) (a v η M : ℝ) (hη : 0 ≤ η)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d), ‖T x‖ ≤ M) :
    Continuous (fun t => ∫ x, finiteExperimentRawDerivative (gridWindowCount d k) n a v η t
      (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  exact finite_experiment_integrated_raw_derivative_continuous
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n a v η ((2 : ℝ) ^ d * η) M
    (gridSampleField d k n η) T (gridSampleField_measurable d k n η) hT
    (Filter.Eventually.of_forall (gridSampleField_norm_le d k n η hη)) hTBound

/-- The score-observable derivative along the actual probability path is
interval integrable, with no regularity assumption on the bounded observable. -/
theorem grid_mixture_score_observable_intervalIntegrable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η M : ℝ)
    (hη : 0 ≤ η) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d), ‖T x‖ ≤ M) :
    IntervalIntegrable (fun t => ∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  apply (grid_mixture_raw_derivative_continuous d k n P.a P.v η M hη T hT hTBound).continuousOn.congr
  intro t ht
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact (finite_experiment_raw_derivative_eq_score (gridWindowCount d k) n P.a P.v η t
    (gridSampleField d k n η x) (T x)
    (grid_response_likelihood_pos C P k n η t hη ht hfield hvariance x)).symm

end NearlyMinimax
