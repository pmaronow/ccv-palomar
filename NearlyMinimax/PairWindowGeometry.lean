module

public import NearlyMinimax.HolderTaylorBridge
public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.GridProjection
public import NearlyMinimax.PairMass


@[expose] public section

/-! Actual regular-grid geometry and design masses for the elementary
same-cell pair-difference estimator. Bounds use the original model density
cap and Hölder regularity, rather than assumed collision probabilities. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax

def elementarySmoothness {d : ℕ} (C : ModelConstants d) : ℝ := min C.smoothness 1

theorem elementarySmoothness_pos {d : ℕ} (C : ModelConstants d) :
    0 < elementarySmoothness C := lt_min C.smoothness_pos (by norm_num)

/-- All admissible regressions have the spatial modulus needed by a first
order pair difference, including smoothness above one. -/
theorem admissible_regression_spatial_modulus {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) :
    |θ.regression x - θ.regression y| ≤
      (2 * ((d : ℝ) + 1) * C.holderBound) *
        euclideanNorm (x - y) ^ elementarySmoothness C := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  have hm := RoughRegime.Model.holderBall_spatial_modulus (euclideanExtension F)
    C.smoothness (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le)
    (euclideanExtension_mem_holderBall C F hreg hNorm)
    (euclideanPoint x) (euclideanPoint y) hx hy
  have hdiff : euclideanPoint x - euclideanPoint y = euclideanPoint (x - y) :=
    ((euclideanCoordinates d).symm.map_sub x y).symm
  rw [hdiff, euclideanPoint_norm] at hm
  simp only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point,
    hcube x hx, hcube y hy] at hm
  unfold elementarySmoothness
  convert hm using 1 <;> ring

theorem regular_grid_index_corner_le (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : 0 ≤ x) :
    (regularGridIndex k hk x : ℝ) / k ≤ x := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfloor := Nat.floor_le (mul_nonneg hkr.le hx)
  have hmin : ((min ⌊(k : ℝ) * x⌋₊ (k - 1) : ℕ) : ℝ) ≤ ⌊(k : ℝ) * x⌋₊ := by
    exact_mod_cast min_le_left ⌊(k : ℝ) * x⌋₊ (k - 1)
  apply (div_le_iff₀ hkr).2
  change ((min ⌊(k : ℝ) * x⌋₊ (k - 1) : ℕ) : ℝ) ≤ x * k
  nlinarith

theorem regular_grid_cell_corner_le {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Covariate d) (hx : x ∈ unitCube d) (i : Fin d) :
    regularGridCorner k (regularGridCell k hk x) i ≤ x i :=
  regular_grid_index_corner_le k hk (x i) (hx i).1

theorem regular_grid_same_cell_radius {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (hcell : regularGridCell k hk x = regularGridCell k hk y) (i : Fin d) :
    |x i - y i| ≤ 1 / k := by
  have hx' := regular_grid_cell_radius k hk x hx i
  have hy' := regular_grid_cell_radius k hk y hy i
  have hxlo := regular_grid_cell_corner_le k hk x hx i
  have hylo := regular_grid_cell_corner_le k hk y hy i
  rw [hcell] at hx'
  rw [hcell] at hxlo
  exact abs_le.2 ⟨by linarith [(abs_le.mp hy').2], by linarith [(abs_le.mp hx').2]⟩

theorem regular_grid_same_cell_regression_difference {d : ℕ}
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) (x y : Covariate d)
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (hcell : regularGridCell k hk x = regularGridCell k hk y) :
    |θ.regression x - θ.regression y| ≤
      (2 * ((d : ℝ) + 1) * C.holderBound) *
        (Real.sqrt (d : ℝ) * (1 / k)) ^ elementarySmoothness C := by
  have hr := euclideanNorm_le_coordinate_radius (x - y) (1 / k)
    (by positivity) (regular_grid_same_cell_radius k hk x y hx hy hcell)
  apply (admissible_regression_spatial_modulus C θ hθ x y hx hy).trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hr
      (elementarySmoothness_pos C).le)
  exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) C.holderBound_pos.le

/-- The probability of each explicit regular-grid label under the actual
admissible design law. -/
def regularGridProbability {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) : ℝ :=
  (designLaw θ).real ((regularGridCell k hk) ⁻¹' {c})

theorem regularGridProbability_nonneg {d : ℕ} (θ : RegressionParameter d)
    (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    0 ≤ regularGridProbability θ k hk c := measureReal_nonneg

theorem regularGridProbability_sum {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    ∑ c, regularGridProbability θ k hk c = 1 := by
  letI := designLaw_isProbability C θ hθ
  unfold regularGridProbability
  have he := sum_measureReal_preimage_singleton (μ := designLaw θ)
    (Finset.univ : Finset (Fin d → Fin k))
    (fun c hc => measurableSet_singleton c |>.preimage (regular_grid_cell_measurable k hk))
  simpa using he

/-- The original density cap gives domination by scaled cube volume. -/
theorem admissible_designLaw_le_cubeVolume {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    designLaw θ ≤ ENNReal.ofReal C.densityUpper • cubeVolume d := by
  unfold designLaw
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hθ.2.2.1] with x hx
  exact ENNReal.ofReal_le_ofReal hx.2

/-- Each cell fiber, restricted to the cube, lies in a closed coordinate
box of side `1/k`. The right-boundary convention preserves this bound. -/
theorem regular_grid_fiber_volume_le {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) :
    cubeVolume d ((regularGridCell k hk) ⁻¹' {c}) ≤ ENNReal.ofReal (1 / (k : ℝ)) ^ d := by
  have hmeas : MeasurableSet ((regularGridCell k hk) ⁻¹' {c}) :=
    (measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk)
  rw [cubeVolume, Measure.restrict_apply hmeas]
  let a : Covariate d := fun i => regularGridCorner k c i
  let b : Covariate d := fun i => regularGridCorner k c i + 1 / k
  have hsub : (regularGridCell k hk) ⁻¹' {c} ∩ unitCube d ⊆ Icc a b := by
    intro x hx
    have hcell : regularGridCell k hk x = c := hx.1
    have hr (i : Fin d) : |x i - regularGridCorner k c i| ≤ 1 / k := by
      simpa only [hcell] using regular_grid_cell_radius k hk x hx.2 i
    constructor
    · intro i
      simpa only [hcell] using regular_grid_cell_corner_le k hk x hx.2 i
    · intro i
      have hi := (abs_le.mp (hr i)).2
      dsimp [b]
      linarith
  apply (measure_mono hsub).trans_eq
  rw [Real.volume_Icc_pi]
  have hside (i : Fin d) : b i - a i = 1 / (k : ℝ) := by dsimp [a, b]; ring
  simp_rw [hside]
  simp

/-- A genuine uniform upper bound for every grid cell probability. -/
theorem regularGridProbability_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) :
    regularGridProbability θ k hk c ≤ C.densityUpper * (1 / (k : ℝ)) ^ d := by
  letI := designLaw_isProbability C θ hθ
  have hdom := Measure.le_iff.1 (admissible_designLaw_le_cubeVolume C θ hθ)
    ((regularGridCell k hk) ⁻¹' {c})
    ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))
  rw [Measure.smul_apply, smul_eq_mul] at hdom
  have hcap : (designLaw θ) ((regularGridCell k hk) ⁻¹' {c}) ≤
      ENNReal.ofReal C.densityUpper * ENNReal.ofReal (1 / (k : ℝ)) ^ d := by
    apply hdom.trans
    gcongr
    exact regular_grid_fiber_volume_le k hk c
  have hu : 0 ≤ C.densityUpper := (by linarith [C.one_lt_densityUpper])
  apply (ENNReal.toReal_mono (by finiteness) hcap).trans_eq
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hu]
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / k)]

theorem regularGridProbability_cap {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) :
    regularGridProbability θ k hk c ≤ C.densityUpper / (k : ℝ) ^ d := by
  convert regularGridProbability_le C θ hθ k hk c using 1 <;> rw [div_pow, one_pow] <;> ring

end NearlyMinimax
