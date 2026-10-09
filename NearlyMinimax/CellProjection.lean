module

public import NearlyMinimax.DesignProjection
public import NearlyMinimax.ModelRegularity


@[expose] public section

open Matrix MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

/-- Evaluation matrix for cellwise constant functions at the actual
sample cell labels. -/
def cellConstantDesign {ι κ : Type*} [DecidableEq κ] (cell : ι → κ) : Matrix ι κ ℝ :=
  fun i j => if cell i = j then 1 else 0

/-- The evaluation matrix fits every cellwise constant vector exactly. -/
theorem cell_constant_design_evaluation {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (cell : ι → κ) (a : κ → ℝ) : cellConstantDesign cell *ᵥ a = fun i => a (cell i) := by
  ext i
  simp only [cellConstantDesign, mulVec, dotProduct, ite_mul, one_mul, zero_mul]
  simp

/-- The actual empirical projection fixes every vector in the column
range, rather than accepting this fitting property as a hypothesis. -/
theorem empirical_design_fixes_evaluation {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ ℝ) (a : κ → ℝ) :
    empiricalDesignProjection B *ᵥ (B *ᵥ a) = B *ᵥ a := by
  have hs := empirical_design_projection_spec B
  have hq : B *ᵥ a ∈ LinearMap.range (empiricalDesignProjection B).mulVecLin := by
    rw [hs.2.2]
    exact ⟨a, rfl⟩
  rcases hq with ⟨v, hv⟩
  change empiricalDesignProjection B *ᵥ v = B *ᵥ a at hv
  rw [← hv, mulVec_mulVec, hs.2.1]

/-- The residual projection annihilates every actually evaluated
cellwise constant approximation. -/
theorem cell_constant_residual_kills {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (cell : ι → κ) (a : κ → ℝ) :
    (1 - empiricalDesignProjection (cellConstantDesign cell)) *ᵥ (fun i => a (cell i)) = 0 := by
  rw [← cell_constant_design_evaluation cell a, sub_mulVec, one_mulVec,
    empirical_design_fixes_evaluation, sub_self]

/-- Cell representatives give a concrete admissible-model approximation
at order zero.  The geometric condition is only the coordinate radius
of the cells; no approximation or residual-risk bound is assumed. -/
theorem admissible_order_zero_cell_residual_bound {d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (horder : C.order = 0) (cell : ι → κ) (x : ι → Covariate d)
    (z : κ → Covariate d) (hx : ∀ i, x i ∈ unitCube d) (hz : ∀ j, z j ∈ unitCube d)
    (h : ℝ) (hh : 0 ≤ h) (hradius : ∀ i j, |x i j - z (cell i) j| ≤ h) :
    projectionEnergy
      ((1 - empiricalDesignProjection (cellConstantDesign cell)) *ᵥ (fun i => θ.regression (x i))) ≤
      Fintype.card ι * (C.holderBound * (Real.sqrt (d : ℝ) * h) ^ C.smoothness) ^ 2 := by
  have hp := empirical_design_projection_spec (cellConstantDesign cell)
  have hres := projection_complement _ hp.1 hp.2.1
  apply projection_approximation_bound _ hres.1 hres.2
    (fun i => θ.regression (x i)) (fun i => θ.regression (z (cell i)))
    (cell_constant_residual_kills cell (fun j => θ.regression (z j)))
    (C.holderBound * (Real.sqrt (d : ℝ) * h) ^ C.smoothness)
  · exact mul_nonneg C.holderBound_pos.le (Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hh) _)
  · intro i
    apply (admissible_regression_order_zero_modulus C θ hθ horder (x i) (z (cell i))
      (hx i) (hz (cell i))).trans
    apply mul_le_mul_of_nonneg_left _ C.holderBound_pos.le
    apply Real.rpow_le_rpow (Real.sqrt_nonneg _)
      (euclideanNorm_le_coordinate_radius (x i - z (cell i)) h hh (hradius i)) C.smoothness_pos.le

/-- Cell-constant evaluation matrices are Borel whenever the cell labels
are measurable, so their exact residual estimator is a data statistic. -/
theorem cell_constant_design_measurable {X ι κ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (cell : X → ι → κ) (hcell : Measurable cell) :
    Measurable (fun x => cellConstantDesign (cell x)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact Measurable.ite (((measurable_pi_apply i).comp hcell) (measurableSet_singleton j))
    measurable_const measurable_const

end NearlyMinimax
