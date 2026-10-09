module

public import NearlyMinimax.GaussianAffineRepresentation
public import NearlyMinimax.PoissonCellField


@[expose] public section

/-! Borel halfspaces and their actual Gaussian--Lebesgue separating measure.
The finite slab contains every hyperplane meeting the local unit cube. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def hyperplaneRadius {d : ℕ} (Z : Covariate d) : ℝ := ∑ r, |Z r|

def hyperplaneCube (d : ℕ) : Set (Covariate d) := {u | ∀ r, |u r| ≤ 1}

def hyperplaneSlab (d : ℕ) : Set (Covariate d × ℝ) :=
  {h | |h.2| ≤ hyperplaneRadius h.1}

def gaussianHyperplaneIntensity (d : ℕ) : Measure (Covariate d × ℝ) :=
  ((standardGaussianPi d).prod volume).restrict (hyperplaneSlab d)

def hyperplaneHalfspace {d : ℕ} (h : Covariate d × ℝ) (u : Covariate d) : Fin 2 :=
  if gaussianPhase u h.1 ≤ h.2 then 0 else 1

theorem hyperplaneRadius_nonneg {d : ℕ} (Z : Covariate d) : 0 ≤ hyperplaneRadius Z :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem hyperplaneRadius_continuous {d : ℕ} : Continuous (hyperplaneRadius (d := d)) := by
  unfold hyperplaneRadius
  fun_prop

theorem hyperplaneSlab_measurable (d : ℕ) : MeasurableSet (hyperplaneSlab d) :=
  measurableSet_le (measurable_snd.abs) (hyperplaneRadius_continuous.measurable.comp measurable_fst)

theorem hyperplaneHalfspace_measurable {d : ℕ} :
    Measurable (Function.uncurry (hyperplaneHalfspace (d := d))) := by
  have hp : Measurable (fun z : (Covariate d × ℝ) × Covariate d =>
      gaussianPhase z.2 z.1.1) := by
    unfold gaussianPhase
    fun_prop
  exact Measurable.ite (measurableSet_le hp measurable_fst.snd) measurable_const measurable_const

theorem hyperplane_phase_bound {d : ℕ} (Z u : Covariate d) (hu : u ∈ hyperplaneCube d) :
    |gaussianPhase u Z| ≤ hyperplaneRadius Z := by
  unfold gaussianPhase hyperplaneRadius
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu r) (abs_nonneg (Z r))

def hyperplaneSeparationSet {d : ℕ} (u v : Covariate d) : Set (Covariate d × ℝ) :=
  {h | hyperplaneHalfspace h u ≠ hyperplaneHalfspace h v}

theorem hyperplaneSeparationSet_measurable {d : ℕ} (u v : Covariate d) :
    MeasurableSet (hyperplaneSeparationSet u v) := by
  exact (measurableSet_eq_fun
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))).compl

theorem hyperplane_separation_slice {d : ℕ} (Z u v : Covariate d) :
    (fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSeparationSet u v =
      Ico (min (gaussianPhase u Z) (gaussianPhase v Z))
        (max (gaussianPhase u Z) (gaussianPhase v Z)) := by
  ext b
  unfold hyperplaneSeparationSet hyperplaneHalfspace
  simp only [mem_preimage, mem_setOf_eq, mem_Ico]
  rcases le_total (gaussianPhase u Z) (gaussianPhase v Z) with huv | hvu
  · rw [min_eq_left huv, max_eq_right huv]
    split_ifs <;> norm_num <;> grind
  · rw [min_eq_right hvu, max_eq_left hvu]
    split_ifs <;> norm_num <;> grind

theorem hyperplane_separation_slice_volume {d : ℕ} (Z u v : Covariate d) :
    volume ((fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSeparationSet u v) =
      ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| := by
  rw [hyperplane_separation_slice, Real.volume_Ico, max_sub_min_eq_abs]
  rw [abs_sub_comm]

theorem hyperplane_separation_subset_slab {d : ℕ} (u v : Covariate d)
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    hyperplaneSeparationSet u v ⊆ hyperplaneSlab d := by
  intro h hh
  have hs : h.2 ∈ Ico (min (gaussianPhase u h.1) (gaussianPhase v h.1))
      (max (gaussianPhase u h.1) (gaussianPhase v h.1)) := by
    exact (Set.ext_iff.mp (hyperplane_separation_slice h.1 u v) h.2).mp hh
  have hu' := abs_le.mp (hyperplane_phase_bound h.1 u hu)
  have hv' := abs_le.mp (hyperplane_phase_bound h.1 v hv)
  exact abs_le.mpr ⟨(le_min hu'.1 hv'.1).trans hs.1,
    hs.2.le.trans (max_le hu'.2 hv'.2)⟩

theorem gaussianHyperplaneIntensity_separation {d : ℕ} (u v : Covariate d)
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
      ∫⁻ Z, ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d := by
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply
    (hyperplaneSeparationSet_measurable u v),
    inter_eq_left.mpr (hyperplane_separation_subset_slab u v hu hv),
    Measure.prod_apply (hyperplaneSeparationSet_measurable u v)]
  simp_rw [hyperplane_separation_slice_volume]

theorem hyperplane_slab_slice {d : ℕ} (Z : Covariate d) :
    (fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSlab d =
      Icc (-hyperplaneRadius Z) (hyperplaneRadius Z) := by
  ext b
  simp only [hyperplaneSlab, mem_preimage, mem_setOf_eq, mem_Icc, abs_le]

theorem gaussianHyperplaneIntensity_univ (d : ℕ) :
    gaussianHyperplaneIntensity d univ =
      ∫⁻ Z, ENNReal.ofReal (2 * hyperplaneRadius Z) ∂standardGaussianPi d := by
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Measure.prod_apply (hyperplaneSlab_measurable d)]
  simp_rw [hyperplane_slab_slice, Real.volume_Icc]
  congr 1
  ext Z
  congr 1
  ring

theorem hyperplane_coordinate_integrable {d : ℕ} (r : Fin d) :
    Integrable (fun Z : Covariate d => Z r) (standardGaussianPi d) := by
  exact integrable_comp_eval (μ := fun _ : Fin d => standardGaussianLine) (i := r) (f := id)
    ((memLp_id_gaussianReal (μ := 0) (v := 1) (1 : ℝ≥0)).integrable (by norm_num))

theorem hyperplaneRadius_integrable (d : ℕ) :
    Integrable (hyperplaneRadius (d := d)) (standardGaussianPi d) := by
  exact integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)

def hyperplaneNormalizingConstant (d : ℕ) : ℝ :=
  ∫ Z, 2 * hyperplaneRadius Z ∂standardGaussianPi d

theorem hyperplaneNormalizingConstant_eq (d : ℕ) :
    hyperplaneNormalizingConstant d =
      2 * d * (∫ z : ℝ, |z| ∂standardGaussianLine) := by
  rw [hyperplaneNormalizingConstant, integral_const_mul]
  unfold hyperplaneRadius
  rw [integral_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)]
  have hi (r : Fin d) : (∫ Z : Covariate d, |Z r| ∂standardGaussianPi d) =
      ∫ z : ℝ, |z| ∂standardGaussianLine := by
    exact integral_comp_eval (μ := fun _ : Fin d => standardGaussianLine)
      (f := fun z : ℝ => |z|) (i := r) (by fun_prop)
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem gaussianHyperplaneIntensity_univ_ofReal (d : ℕ) :
    gaussianHyperplaneIntensity d univ = ENNReal.ofReal (hyperplaneNormalizingConstant d) := by
  rw [gaussianHyperplaneIntensity_univ]
  exact (ofReal_integral_eq_lintegral_ofReal ((hyperplaneRadius_integrable d).const_mul 2)
    (Filter.Eventually.of_forall (fun Z => mul_nonneg (by norm_num) (hyperplaneRadius_nonneg Z)))).symm

instance gaussianHyperplaneIntensity_finite (d : ℕ) :
    IsFiniteMeasure (gaussianHyperplaneIntensity d) := by
  constructor
  rw [gaussianHyperplaneIntensity_univ_ofReal]
  exact ENNReal.ofReal_lt_top

theorem hyperplanePhase_integrable {d : ℕ} (u : Covariate d) :
    Integrable (gaussianPhase u) (standardGaussianPi d) := by
  exact integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).const_mul (u r))

theorem gaussianHyperplaneIntensity_separation_ofReal {d : ℕ} (u v : Covariate d)
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
      ENNReal.ofReal (∫ Z, |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d) := by
  rw [gaussianHyperplaneIntensity_separation u v hu hv]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((hyperplanePhase_integrable u).sub (hyperplanePhase_integrable v)).abs
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm

end NearlyMinimax
