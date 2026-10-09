module

public import NearlyMinimax.LowSmoothnessRestriction
public import NearlyMinimax.LowSmoothnessWindows


@[expose] public section

/-! The actual grid prior's design-dependent conditional score energies. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

def gridWindowCount (d k : ℕ) : ℕ := (k + 1) ^ d

def gridWindowIndexEquiv (d k : ℕ) : Fin (gridWindowCount d k) ≃ (Fin d → Fin (k + 1)) :=
  (Fintype.equivFinOfCardEq (by simp [gridWindowCount])).symm

def indexedGridWindow (d k : ℕ) (j : Fin (gridWindowCount d k)) : Covariate d → ℝ :=
  gridTensorWindow d k (gridWindowIndexEquiv d k j)

def indexedGridPatch (d k : ℕ) (j : Fin (gridWindowCount d k)) : Set (Covariate d) :=
  gridPatch d k (gridWindowIndexEquiv d k j)

def indexedGridField (d k : ℕ) (η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (x : Covariate d) : ℝ := η * ∑ j, indexedGridWindow d k j x * ternaryValue 1 (ξ j)

theorem indexedGridField_eq (d k : ℕ) (η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3) :
    indexedGridField d k η ξ =
      gridPriorField d k η (fun j => ξ ((gridWindowIndexEquiv d k).symm j)) := by
  funext x
  unfold indexedGridField gridPriorField
  congr 1
  exact Fintype.sum_equiv (gridWindowIndexEquiv d k) _ _ (fun j => by simp [indexedGridWindow])

theorem indexedGridField_continuous (d k : ℕ) (η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3) :
    Continuous (indexedGridField d k η ξ) := by
  rw [indexedGridField_eq]
  exact gridPriorField_continuous _ _ _ _

theorem indexedGridField_abs_bound (d k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Covariate d) :
    |indexedGridField d k η ξ x| ≤ (2 : ℝ) ^ d * η := by
  rw [indexedGridField_eq]
  exact gridPriorField_abs_bound _ _ _ hη _ x

def gridSampleWeights (d k n : ℕ) (x : Fin n → Covariate d) :
    Fin n → Fin (gridWindowCount d k) → ℝ := fun i j => indexedGridWindow d k j (x i)

theorem grid_latent_regression_eq (d k n : ℕ) (η : ℝ) (x : Fin n → Covariate d)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
    latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ i =
      indexedGridField d k η ξ (x i) := by
  simp [latentRegression, indexedGridField, gridSampleWeights]

theorem grid_sample_squared_partition (d k n : ℕ) (x : Fin n → Covariate d) (i : Fin n) :
    (∑ j, gridSampleWeights d k n x i j ^ 2) = 1 := by
  have h := Fintype.sum_equiv (gridWindowIndexEquiv d k)
    (fun j => indexedGridWindow d k j (x i) ^ 2) (fun j => gridTensorWindow d k j (x i) ^ 2)
    (fun _ => rfl)
  exact h.trans (gridTensorWindow_square_partition d k (x i))

theorem grid_modified_regression_abs_bound (d k n : ℕ) (η u : ℝ) (hη : 0 ≤ η)
    (x : Fin n → Covariate d) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (j : Fin (gridWindowCount d k)) (i : Fin n) (hu : u ∈ Icc (-1 : ℝ) 1) :
    |latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j i +
      η * gridSampleWeights d k n x i j * u| ≤ ((2 : ℝ) ^ d + 2) * η := by
  let z := ternaryValue 1 (ξ j)
  have hz : |z| ≤ 1 := ternaryValue_one_abs_le (ξ j)
  have hw : |gridSampleWeights d k n x i j| ≤ 1 := by
    change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
    rw [abs_of_nonneg (gridTensorWindow_nonneg d k (gridWindowIndexEquiv d k j) (x i))]
    exact gridTensorWindow_le_one _ _ _ _
  have hdiff : |u - z| ≤ 2 := by
    have h := abs_sub_le u 0 z
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [abs_le.mpr hu]
  have heq : latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j i + η * gridSampleWeights d k n x i j * u =
        indexedGridField d k η ξ (x i) + η * gridSampleWeights d k n x i j * (u - z) := by
    rw [← grid_latent_regression_eq, latent_regression_decomposition]
    dsimp [z]
    ring
  rw [heq]
  have hterm : |η * gridSampleWeights d k n x i j * (u - z)| ≤ 2 * η := by
    rw [abs_mul, abs_mul, abs_of_nonneg hη]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hw hη) hdiff (abs_nonneg _) (by positivity : 0 ≤ η * 1)
    simpa only [mul_one, mul_comm] using h
  exact (abs_add_le _ _).trans (by nlinarith [indexedGridField_abs_bound d k η hη ξ (x i)])

def gridCoordinateEnergy (d k n : ℕ) (a V η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (x : Fin n → Covariate d) : ℝ :=
  patchExpectedScoreEnergy n a V η
    (latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j)
    (fun i => gridSampleWeights d k n x i j) (ternaryValue 1 (ξ j))

theorem grid_sample_weight_measurable (d k n : ℕ) (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x : Fin n → Covariate d => gridSampleWeights d k n x i j) :=
  ((gridTensorWindow_continuous d k (gridWindowIndexEquiv d k j)).comp
    (continuous_apply i)).measurable

theorem grid_excluded_field_measurable (d k n : ℕ) (η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x : Fin n → Covariate d =>
      latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j i) := by
  unfold latentRegressionWithout
  exact measurable_const.add ((Finset.measurable_sum _
    (fun l _ => (grid_sample_weight_measurable d k n l i).mul_const _)).const_mul _)

/-- Actual coordinate score energy integrated over the complete uniform-design
sample. The observations outside the patch have already been cancelled. -/
theorem grid_coordinate_design_energy_bound {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (hk : 0 < k) (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    (∫ x : Fin n → Covariate d, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
      ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
        Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 *
          (n * (2 / (k : ℝ)) ^ d) ^ 2 := by
  let _ := cubeVolume_isProbability d
  let g : (Fin n → Covariate d) → Fin n → ℝ := fun x =>
    latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j
  let w : (Fin n → Covariate d) → Fin n → ℝ := fun x i => gridSampleWeights d k n x i j
  let A := indexedGridPatch d k j
  let z := ternaryValue 1 (ξ j)
  have hz : z ∈ Icc (-1 : ℝ) 1 := abs_le.mp (ternaryValue_one_abs_le (ξ j))
  have hreg (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :
      |g x i + η * w x i * u| ≤ P.ρ :=
    (grid_modified_regression_abs_bound d k n η u hη x ξ j i hu).trans hfield
  have hlegal (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :=
    P.path_legality η t (g x i + η * w x i * u) ht hvariance (hreg x u hu i)
  have hp (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) (y : Fin 3) :
      0 < ternaryMass P.a (g x i + η * w x i * u) (P.variancePath η t) y :=
    P.c_pos.trans_le ((hlegal x u hu i).2.2.1 y)
  have hvol : (cubeVolume d).real A ≤ (2 / (k : ℝ)) ^ d := gridPatch_cube_probability_bound d k _ hk
  have hmean' : n * (cubeVolume d).real A ≤ 1 :=
    (mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg n)).trans hmean
  have hbound := iid_design_full_patch_score_energy_bound (cubeVolume d) n A
    (gridPatch_measurable d k _) P.a (P.variancePath η t) η z P.ρ P.c g w
    (grid_excluded_field_measurable d k n η ξ j) (grid_sample_weight_measurable d k n j)
    P.a_pos P.ρ_pos.le P.c_pos hz hmean'
    (fun x i hi => gridTensorWindow_zero_outside_patch d k (gridWindowIndexEquiv d k j) (x i) hi)
    (fun x i _ => by
      change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
      rw [abs_of_nonneg (gridTensorWindow_nonneg d k _ _)]; exact gridTensorWindow_le_one d k _ _)
    (fun x u hu i _ => hreg x u hu i)
    (fun x u hu i _ y => ⟨(hp x u hu i y).le,
      ternary_mass_le_one P.a _ _ P.a_pos.ne' (fun b => (hp x u hu i b).le) y⟩)
    (fun x i _ y => (hlegal x z hz i).2.2.1 y) (fun x i y => hp x z hz i y)
  apply hbound.trans
  gcongr

def gridFullScoreEnergy (d k n : ℕ) (a V η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (x : Fin n → Covariate d) : ℝ :=
  ∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V
    (latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)) ξ y *
    (finiteExperimentScore (gridWindowCount d k) n a V η
      (latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)) ξ y) ^ 2

theorem indexed_grid_observed_patch_degree (d k n : ℕ) (x : Fin n → Covariate d)
    (j : Fin (gridWindowCount d k)) :
    (Finset.univ.filter fun l : Fin (gridWindowCount d k) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k l)).card ≤ 5 ^ d := by
  have heq := Finset.card_equiv (gridWindowIndexEquiv d k) (s := Finset.univ.filter fun l =>
    ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k j)
      (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k l))
    (t := Finset.univ.filter fun l =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k (gridWindowIndexEquiv d k j))
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l))
    (fun _ => by
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      rfl)
  rw [heq]
  exact grid_observed_patch_degree d k n x _

theorem grid_full_score_conditional_energy_bound (d k n : ℕ) (a V η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d)
    (ha : a ≠ 0) (hp : ∀ i y, 0 < ternaryMass a (indexedGridField d k η ξ (x i)) V y) :
    gridFullScoreEnergy d k n a V η ξ x ≤ (5 : ℝ) ^ d *
      ∑ j, gridCoordinateEnergy d k n a V η ξ j x := by
  let f := latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)
  let S : Fin (gridWindowCount d k) → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => x i ∈ indexedGridPatch d k j)
  have hpos : ∀ i y, 0 < ternaryMass a (f ξ i) V y := by
    intro i y
    simpa [f, grid_latent_regression_eq] using hp i y
  have h := latent_full_score_variance_bound (gridWindowCount d k) n a V η (fun _ => 0)
    (gridSampleWeights d k n x) ξ S (5 ^ d)
    (fun j i hi => gridTensorWindow_zero_outside_patch d k _ (x i) (by
      intro hmem
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩))
    (grid_sample_squared_partition d k n x)
    (indexed_grid_observed_patch_degree d k n x) ha hpos
  simp_rw [ternary_index_product_integral] at h
  change gridFullScoreEnergy d k n a V η ξ x ≤ (5 ^ d : ℕ) *
    ∑ j, ∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V f ξ y *
      (finiteCoordinateScore (gridWindowCount d k) n a V η f (gridSampleWeights d k n x) ξ y j) ^ 2 at h
  have hcoord (j : Fin (gridWindowCount d k)) :
      (∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V f ξ y *
        (finiteCoordinateScore (gridWindowCount d k) n a V η f (gridSampleWeights d k n x) ξ y j) ^ 2) =
        gridCoordinateEnergy d k n a V η ξ j x := by
    unfold gridCoordinateEnergy patchExpectedScoreEnergy
    apply Finset.sum_congr rfl
    intro y _
    rw [latent_coordinate_score_eq_patch]
    congr 1
    simp only [finiteResponseLikelihood, patchResponseProduct, f]
    simp_rw [latent_regression_decomposition (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j]
  simp_rw [hcoord] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

theorem grid_full_score_energy_measurable (d k n : ℕ) (a V η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) :
    Measurable (gridFullScoreEnergy d k n a V η ξ) := by
  let f : (Fin n → Covariate d) → (Fin (gridWindowCount d k) → Fin 3) → Fin n → ℝ :=
    fun x => latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)
  have hq (ξ' : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) (y : Fin 3) :
      Measurable (fun x => ternaryMass a (f x ξ' i) V y) := by
    apply ternaryMass_measurable_comp
    simpa only [f, grid_latent_regression_eq, Function.comp_def] using
      ((indexedGridField_continuous d k η ξ').comp (continuous_apply i)).measurable
  have hL (ξ' : Fin (gridWindowCount d k) → Fin 3) (y : Fin n → Fin 3) :
      Measurable (fun x => finiteResponseLikelihood (gridWindowCount d k) n a V (f x) ξ' y) :=
    Finset.measurable_prod _ (fun i _ => hq ξ' i (y i))
  have hU (y : Fin n → Fin 3) (i : Fin n) :
      Measurable (fun x => finiteResponseVarianceTerm (gridWindowCount d k) n a V (f x) ξ y i) :=
    (Finset.measurable_prod _ (fun l _ => hq ξ l (y l))).const_mul _
  have hD (y : Fin n → Fin 3) (j : Fin (gridWindowCount d k)) :
      Measurable (fun x => latentDifference (gridWindowCount d k) j
        (fun ξ' => finiteResponseLikelihood (gridWindowCount d k) n a V (f x) ξ' y) ξ) :=
    (((hL (Function.update ξ j 2) y).const_mul (1 / 2)).add
      ((hL (Function.update ξ j 0) y).const_mul (1 / 2))).sub (hL (Function.update ξ j 1) y)
  have hR (y : Fin n → Fin 3) :
      Measurable (fun x => finiteExperimentScore (gridWindowCount d k) n a V η (f x) ξ y) :=
    ((Finset.measurable_sum _ (fun j _ => hD y j)).sub
      ((Finset.measurable_sum _ (fun i _ => hU y i)).const_mul (η ^ 2))).div (hL ξ y)
  exact Finset.measurable_sum _ (fun y _ => (hL ξ y).mul ((hR y).pow_const 2))

theorem grid_coordinate_energy_integrable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    Integrable (gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  let g : (Fin n → Covariate d) → Fin n → ℝ := fun x =>
    latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j
  let w : (Fin n → Covariate d) → Fin n → ℝ := fun x i => gridSampleWeights d k n x i j
  let z := ternaryValue 1 (ξ j)
  have hz : z ∈ Icc (-1 : ℝ) 1 := abs_le.mp (ternaryValue_one_abs_le (ξ j))
  have hreg (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :
      |g x i + η * w x i * u| ≤ P.ρ :=
    (grid_modified_regression_abs_bound d k n η u hη x ξ j i hu).trans hfield
  have hlegal (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :=
    P.path_legality η t (g x i + η * w x i * u) ht hvariance (hreg x u hu i)
  have hp (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) (y : Fin 3) :
      0 < ternaryMass P.a (g x i + η * w x i * u) (P.variancePath η t) y :=
    P.c_pos.trans_le ((hlegal x u hu i).2.2.1 y)
  exact patch_expected_score_energy_integrable _ n P.a (P.variancePath η t) η z P.ρ P.c g w
    (grid_excluded_field_measurable d k n η ξ j) (grid_sample_weight_measurable d k n j)
    P.a_pos P.ρ_pos.le P.c_pos hz
    (fun x i => by
      change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
      rw [abs_of_nonneg (gridTensorWindow_nonneg d k _ _)]; exact gridTensorWindow_le_one d k _ _)
    hreg (fun x u hu i y => ⟨(hp x u hu i y).le,
      ternary_mass_le_one P.a _ _ P.a_pos.ne' (fun b => (hp x u hu i b).le) y⟩)
    (fun x i y => (hlegal x z hz i).2.2.1 y)

theorem grid_response_positive {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    ∀ i y, 0 < ternaryMass P.a (indexedGridField d k η ξ (x i)) (P.variancePath η t) y := by
  intro i y
  have hF : |indexedGridField d k η ξ (x i)| ≤ P.ρ :=
    (indexedGridField_abs_bound d k η hη ξ (x i)).trans (by nlinarith)
  exact P.c_pos.trans_le ((P.path_legality η t _ ht hvariance hF).2.2.1 y)

theorem grid_full_score_energy_integrable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    Integrable (gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  have hI := (integrable_finsetSum (Finset.univ : Finset (Fin (gridWindowCount d k))) (fun j _ =>
    grid_coordinate_energy_integrable C P k n η t ξ j hη ht hfield hvariance)).const_mul ((5 : ℝ) ^ d)
  apply hI.mono' (grid_full_score_energy_measurable d k n P.a (P.variancePath η t) η ξ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hp := grid_response_positive C P k n η t ξ x hη ht hfield hvariance
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact grid_full_score_conditional_energy_bound d k n P.a (P.variancePath η t) η ξ x P.a_pos.ne' hp
  · exact Finset.sum_nonneg (fun y _ => mul_nonneg
      (Finset.prod_nonneg (fun i _ => by simpa [grid_latent_regression_eq] using (hp i (y i)).le))
      (sq_nonneg _))

theorem grid_full_score_design_energy_bound {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (hk : 0 < k)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    (∫ x : Fin n → Covariate d, gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
      (5 : ℝ) ^ d * gridWindowCount d k *
        (ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
          Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2) := by
  let μ := Measure.pi (fun _ : Fin n => cubeVolume d)
  have hcoords (j : Fin (gridWindowCount d k)) :=
    grid_coordinate_energy_integrable C P k n η t ξ j hη ht hfield hvariance
  calc
    _ ≤ ∫ x, (5 : ℝ) ^ d * ∑ j, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x ∂μ :=
      integral_mono (grid_full_score_energy_integrable C P k n η t ξ hη ht hfield hvariance)
        ((integrable_finsetSum _ (fun j _ => hcoords j)).const_mul _)
        (fun x => grid_full_score_conditional_energy_bound d k n P.a (P.variancePath η t) η ξ x
          P.a_pos.ne' (grid_response_positive C P k n η t ξ x hη ht hfield hvariance))
    _ = (5 : ℝ) ^ d * ∑ j, ∫ x, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hcoords j)]
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (5 : ℝ) ^ d)
      calc
        _ ≤ ∑ _j : Fin (gridWindowCount d k),
            ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
              Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 *
                (n * (2 / (k : ℝ)) ^ d) ^ 2 := Finset.sum_le_sum (fun j _ =>
          grid_coordinate_design_energy_bound C P k n η t ξ j hk hη ht hfield hvariance hmean)
        _ = _ := by simp

/-- The actual latent-prior, design, and response score energy. -/
def gridPriorScoreEnergy (d k n : ℕ) (a v η t : ℝ) : ℝ :=
  ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ *
    ∫ x : Fin n → Covariate d, gridFullScoreEnergy d k n a (v - η ^ 2 * t) η ξ x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)

/-- Uniform full score budget for the actual prior and the actual IID design.
Every energy bound is derived from the ternary likelihood, count law, and
window support geometry. -/
theorem grid_prior_score_energy_bound {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ) (hk : 1 ≤ k)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    gridPriorScoreEnergy d k n P.a P.v η t ≤
      (40 : ℝ) ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
        Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * n ^ 2 * η ^ 4 / (k : ℝ) ^ d := by
  let K := ternaryScoreExponentialConstant P.a P.ρ P.c
  let B := (5 : ℝ) ^ d * gridWindowCount d k *
    (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2)
  have hkp : 0 < k := by omega
  have hbudget : gridPriorScoreEnergy d k n P.a P.v η t ≤ B := by
    unfold gridPriorScoreEnergy
    calc
      _ ≤ ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ * B := by
        apply Finset.sum_le_sum
        intro ξ _
        exact mul_le_mul_of_nonneg_left
          (grid_full_score_design_energy_bound C P k n η t ξ hkp hη ht hfield hvariance hmean)
          (Finset.prod_nonneg (fun i _ => activation_prior_nonnegative t ht.1 ht.2 (ξ i)))
      _ = B := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hkp
  have hm : (gridWindowCount d k : ℝ) ≤ (2 * (k : ℝ)) ^ d := by
    have hk1 : (k : ℝ) + 1 ≤ 2 * k := by exact_mod_cast (by omega : k + 1 ≤ 2 * k)
    simpa only [gridWindowCount, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k + 1) hk1 d
  calc
    _ ≤ B := hbudget
    _ ≤ (5 : ℝ) ^ d * (2 * (k : ℝ)) ^ d *
        (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / (k : ℝ)) ^ d) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity)
    _ = _ := by
      rw [show (40 : ℝ) = 5 * 2 ^ 3 by norm_num]
      have htwo : ((2 : ℝ) ^ 3) ^ d = ((2 : ℝ) ^ d) ^ 3 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 d]
      simp only [mul_pow, div_pow, htwo]
      dsimp [K]
      field_simp [ne_of_gt hkr]

/-- The actual model parameter in each latent state of the indexed grid prior. -/
def gridPathParameter {d : ℕ} (C : ModelConstants d) (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) (η t : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    RegressionParameter d :=
  P.pathParameter (indexedGridField d k η ξ) (indexedGridField_continuous d k η ξ) η t ht hvariance
    (fun x => (indexedGridField_abs_bound d k η hη ξ x).trans (by nlinarith))

theorem gridPathParameter_admissible {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1)
    (hb : 0 ≤ b) (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound) :
    Admissible C (gridPathParameter C P k η t ξ hη ht hfield hvariance) := by
  have horder : C.order = 0 := by
    have ho : (C.order : ℝ) < 1 := C.order_lt.trans_le hs1
    have hnat : C.order < 1 := by exact_mod_cast ho
    omega
  have hηb : η ≤ b := by
    rw [hscale]
    exact div_le_self hb (Real.one_le_rpow (by exact_mod_cast hk) C.smoothness_pos.le)
  apply P.pathParameter_admissible_order_zero _ _ η t ht hvariance _ horder
    ((2 : ℝ) ^ d * b) ((68 * (2 : ℝ) ^ d * (d + 1)) * b)
    (by positivity) (by positivity) (by nlinarith [hholder])
  · intro x
    exact (indexedGridField_abs_bound d k η hη ξ x).trans (mul_le_mul_of_nonneg_left hηb (by positivity))
  · intro x y
    rw [hscale, indexedGridField_eq]
    exact gridPriorField_holder_bound d k C.smoothness b hk C.smoothness_pos.le hs1 hb _ x y

end NearlyMinimax
