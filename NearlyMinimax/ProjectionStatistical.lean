module

public import NearlyMinimax.GridProjectionRisk
public import NearlyMinimax.Risk


@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace NearlyMinimax

/-- The actual regular-grid residual estimator on the model sample space. -/
def regularGridEstimator (d n k : ℕ) (hk : 0 < k) : Estimator d n :=
  ⟨fun z => projectionEstimator
    (1 - empiricalDesignProjection (cellConstantDesign
      (fun i => regularGridCell k hk (z i).1)))
    (fun i => (z i).2), by
    apply regular_grid_residual_estimator_measurable k hk
    · fun_prop
    · fun_prop⟩

/-- A uniform stochastic constant depending only on the fixed model. -/
def gridProjectionConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  4 * max C.fourthBound (2 * C.varianceUpper ^ 2) +
    32 * C.varianceUpper * C.holderBound ^ 2

/-- The proved deterministic cell approximation contribution. -/
def gridProjectionBias {d : ℕ} (C : ModelConstants d) (k : ℕ) : ℝ :=
  4 * (C.holderBound * (Real.sqrt (d : ℝ) * (1 / k)) ^ C.smoothness) ^ 4

theorem gridProjectionConstant_nonneg {d : ℕ} (C : ModelConstants d) :
    0 ≤ gridProjectionConstant C := by
  have hV : 0 < C.varianceUpper := C.varianceLower_pos.trans C.variance_interval
  have hm : 0 ≤ max C.fourthBound (2 * C.varianceUpper ^ 2) :=
    (by positivity : 0 ≤ 2 * C.varianceUpper ^ 2).trans (le_max_right _ _)
  unfold gridProjectionConstant
  positivity

/-- The variance-specific conditional constant is bounded by the model
constant, using the actual admissible variance interval. -/
theorem admissible_grid_projection_constant_bound {d : ℕ}
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ) :
    4 * max C.fourthBound (2 * θ.variance ^ 2) +
      32 * θ.variance * C.holderBound ^ 2 ≤ gridProjectionConstant C := by
  have hV0 : 0 ≤ θ.variance := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hV : θ.variance ≤ C.varianceUpper := hθ.2.2.2.2.2.2.1
  have hVupper0 : 0 ≤ C.varianceUpper := hV0.trans hV
  have hsq := (sq_le_sq₀ hV0 hVupper0).mpr hV
  have hm := max_le_max_left C.fourthBound (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2))
  have hlinear := mul_le_mul_of_nonneg_right hV (by positivity : 0 ≤ 32 * C.holderBound ^ 2)
  unfold gridProjectionConstant
  nlinarith

/-- The fixed-design conditional theorem expressed in the extended-real
loss used by the original model. Fourth moments prove square integrability;
there is no assumption that the desired loss integral is finite or bounded. -/
theorem regular_grid_conditional_lintegral_bound
    {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (horder : C.order = 0) (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d ≤ (n : ℝ) / 2)
    (x : Fin n → Covariate d) (hx : ∀ i, x i ∈ unitCube d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : Fin n → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = θ.variance)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C.fourthBound) :
    (∫⁻ ω, ENNReal.ofReal
      (((regularGridEstimator d n k hk).val
        (fun i => (x i, θ.regression (x i) + ε i ω)) - θ.variance) ^ 2) ∂μ) ≤
      ENNReal.ofReal (gridProjectionConstant C / n + gridProjectionBias C k) := by
  let B := cellConstantDesign (fun i => regularGridCell k hk (x i))
  let A := 1 - empiricalDesignProjection B
  let f := fun i => θ.regression (x i)
  have hP := empirical_design_projection_spec B
  have hA := projection_complement (empiricalDesignProjection B) hP.1 hP.2.1
  have hX := projection_estimator_memLp_two μ A hA.1 f (fun ω i => ε i ω)
    (fun i => (hε i).mono_exponent (by norm_num))
    (independent_error_product_memLp_two μ ε hε)
  have hsq : Integrable
      (fun ω => (projectionEstimator A (f + fun i => ε i ω) - θ.variance) ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
      (hX.sub (memLp_const θ.variance)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hfixed := independent_regular_grid_projection_mse_bound C θ hθ horder k hk
    (by simpa using hn) (by simpa using hcolumns) x hx μ ε hε hind hmean hsecond hfourth
  have huniform :
      (∫ ω, (projectionEstimator A (f + fun i => ε i ω) - θ.variance) ^ 2 ∂μ) ≤
      gridProjectionConstant C / n + gridProjectionBias C k := by
    apply hfixed.trans
    have hdiv := div_le_div_of_nonneg_right (admissible_grid_projection_constant_bound C θ hθ)
      (Nat.cast_nonneg n)
    simpa only [Fintype.card_fin, gridProjectionBias] using
      add_le_add hdiv (le_refl (gridProjectionBias C k))
  change (∫⁻ ω, ENNReal.ofReal
    ((projectionEstimator A (f + fun i => ε i ω) - θ.variance) ^ 2) ∂μ) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal huniform

end NearlyMinimax
