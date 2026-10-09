module

public import NearlyMinimax.GridProjection
public import NearlyMinimax.ProjectionRates


@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

/-- An actual order-zero admissible regression, fitted by the explicit
regular-grid cell design, satisfies the projection upper risk bound
under any independent centered errors with the model moments.  The
regression approximation and degree bounds are proved from the actual
model and the actual grid construction. -/
theorem independent_regular_grid_projection_mse_bound
    {d : ℕ} {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (horder : C.order = 0) (k : ℕ) (hk : 0 < k)
    (hn : 0 < Fintype.card ι) (hcolumns : (k : ℝ) ^ d ≤ (Fintype.card ι : ℝ) / 2)
    (x : ι → Covariate d) (hx : ∀ i, x i ∈ unitCube d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = θ.variance)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C.fourthBound) :
    (∫ ω, (projectionEstimator
      (1 - empiricalDesignProjection (cellConstantDesign (fun i => regularGridCell k hk (x i))))
      ((fun i => θ.regression (x i)) + fun i => ε i ω) - θ.variance) ^ 2 ∂μ) ≤
      (4 * max C.fourthBound (2 * θ.variance ^ 2) +
        32 * θ.variance * C.holderBound ^ 2) / Fintype.card ι +
      4 * (C.holderBound * (Real.sqrt (d : ℝ) * (1 / k)) ^ C.smoothness) ^ 4 := by
  let B := cellConstantDesign (fun i => regularGridCell k hk (x i))
  have hP := empirical_design_projection_spec B
  have hA := projection_complement (empiricalDesignProjection B) hP.1 hP.2.1
  have hdegree : (Fintype.card ι : ℝ) / 2 ≤ (1 - empiricalDesignProjection B).trace := by
    have hdeg := regular_grid_residual_degrees k hk x
    change (Fintype.card ι : ℝ) - (k : ℝ) ^ d ≤ (1 - empiricalDesignProjection B).trace at hdeg
    linarith
  apply independent_projection_half_degrees_mse μ _ hA.1 hA.2 hn hdegree
    (fun i => θ.regression (x i)) ε θ.variance C.fourthBound C.holderBound
    (C.holderBound * (Real.sqrt (d : ℝ) * (1 / k)) ^ C.smoothness)
    (C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1) C.holderBound_pos.le
  · exact fun i => admissible_regression_value_bound C θ hθ (x i) (hx i)
  · exact regular_grid_projection_residual_bound C θ hθ horder k hk x hx
  · exact hε
  · exact hind
  · exact hmean
  · exact hsecond
  · exact hfourth

end NearlyMinimax
