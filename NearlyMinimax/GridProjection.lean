module

public import NearlyMinimax.CellProjection


@[expose] public section

open Matrix MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

/-- A regular-grid cell index, with the cube's right endpoint assigned
to the last cell. -/
def regularGridIndex (k : ℕ) (hk : 0 < k) (x : ℝ) : Fin k :=
  ⟨min ⌊(k : ℝ) * x⌋₊ (k - 1), (min_le_right _ _).trans_lt (by omega)⟩

/-- Product cell label of a covariate. -/
def regularGridCell {d : ℕ} (k : ℕ) (hk : 0 < k) (x : Covariate d) : Fin d → Fin k :=
  fun i => regularGridIndex k hk (x i)

/-- The lower corner of an actual regular-grid cell. -/
def regularGridCorner {d : ℕ} (k : ℕ) (c : Fin d → Fin k) : Covariate d :=
  fun i => (c i : ℝ) / k

/-- The explicit floor-based label and corner have the claimed cell
radius, including observations on the cube's right boundary. -/
theorem regular_grid_index_radius (k : ℕ) (hk : 0 < k) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - (regularGridIndex k hk x : ℝ) / k| ≤ 1 / k := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  let m := ⌊(k : ℝ) * x⌋₊
  have hfloor : (m : ℝ) ≤ (k : ℝ) * x := Nat.floor_le (mul_nonneg hkreal.le hx0)
  have hmin : ((min m (k - 1) : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_left m (k - 1)
  have hcorner : (regularGridIndex k hk x : ℝ) / k ≤ x := by
    apply (div_le_iff₀ hkreal).mpr
    change ((min m (k - 1) : ℕ) : ℝ) ≤ x * k
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hcorner)]
  have hsub : x - (regularGridIndex k hk x : ℝ) / k =
      (x * k - (regularGridIndex k hk x : ℝ)) / k := by field_simp
  rw [hsub]
  apply (div_le_div_iff_of_pos_right hkreal).mpr
  change x * k - ((min m (k - 1) : ℕ) : ℝ) ≤ 1
  by_cases hm : m ≤ k - 1
  · rw [min_eq_left hm]
    have hlt : (k : ℝ) * x < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith
  · have hm' : k - 1 ≤ m := by omega
    rw [min_eq_right hm', Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right hx1 hkreal.le]

/-- Every chosen cell corner belongs to the model's design cube. -/
theorem regular_grid_corner_mem_cube {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) : regularGridCorner k c ∈ unitCube d := by
  intro i
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨div_nonneg (Nat.cast_nonneg _) hkreal.le, ?_⟩
  apply (div_le_iff₀ hkreal).mpr
  have hi : ((c i).val : ℝ) < k := by exact_mod_cast (c i).isLt
  simpa only [one_mul] using hi.le

/-- The regular-grid radius follows directly from the covariate's cube
membership, with no assumed approximation property. -/
theorem regular_grid_cell_radius {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Covariate d) (hx : x ∈ unitCube d) (i : Fin d) :
    |x i - regularGridCorner k (regularGridCell k hk x) i| ≤ 1 / k :=
  regular_grid_index_radius k hk (x i) (hx i).1 (hx i).2

/-- The explicit grid construction proves the actual order-zero model
residual approximation, for arbitrary sample design points in the cube. -/
theorem regular_grid_projection_residual_bound {d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (horder : C.order = 0)
    (k : ℕ) (hk : 0 < k) (x : ι → Covariate d) (hx : ∀ i, x i ∈ unitCube d) :
    projectionEnergy
      ((1 - empiricalDesignProjection (cellConstantDesign (fun i => regularGridCell k hk (x i)))) *ᵥ
        (fun i => θ.regression (x i))) ≤
      Fintype.card ι * (C.holderBound * (Real.sqrt (d : ℝ) * (1 / k)) ^ C.smoothness) ^ 2 := by
  apply admissible_order_zero_cell_residual_bound C θ hθ horder
    (fun i => regularGridCell k hk (x i)) x (regularGridCorner k) hx
    (regular_grid_corner_mem_cube k hk) (1 / k) (by positivity)
  intro i j
  exact regular_grid_cell_radius k hk (x i) (hx i) j

/-- This cellwise fit has at most `k^d` columns. -/
theorem regular_grid_residual_degrees {d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (k : ℕ) (hk : 0 < k) (x : ι → Covariate d) :
    (Fintype.card ι : ℝ) - k ^ d ≤
      (1 - empiricalDesignProjection (cellConstantDesign (fun i => regularGridCell k hk (x i)))).trace := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    empirical_design_residual_degrees (cellConstantDesign (fun i => regularGridCell k hk (x i)))

/-- Grid labels are Borel despite the floor discontinuities. -/
theorem regular_grid_index_measurable (k : ℕ) (hk : 0 < k) :
    Measurable (regularGridIndex k hk) := by
  let f : ℕ → Fin k := fun m => ⟨min m (k - 1), (min_le_right _ _).trans_lt (by omega)⟩
  exact (measurable_of_countable f).comp ((measurable_const.mul measurable_id).nat_floor)

theorem regular_grid_cell_measurable {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Measurable (regularGridCell (d := d) k hk) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (regular_grid_index_measurable k hk).comp (measurable_pi_apply i)

/-- The explicit regular-grid estimator is a Borel function of the
actual covariates and responses. -/
theorem regular_grid_residual_estimator_measurable {X ι : Type*} {d : ℕ}
    [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 0 < k) (x : X → ι → Covariate d) (Y : X → ι → ℝ)
    (hx : Measurable x) (hY : Measurable Y) :
    Measurable (fun ω => projectionEstimator
      (1 - empiricalDesignProjection (cellConstantDesign (fun i => regularGridCell k hk (x ω i))))
      (Y ω)) := by
  apply empirical_residual_estimator_measurable _ Y _ hY
  apply cell_constant_design_measurable
  apply measurable_pi_iff.mpr
  intro i
  exact (regular_grid_cell_measurable k hk).comp ((measurable_pi_apply i).comp hx)

end NearlyMinimax
