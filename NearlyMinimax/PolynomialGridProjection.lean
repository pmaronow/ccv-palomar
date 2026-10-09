module

public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.GridProjection
public import NearlyMinimax.HolderTaylorBridge
public import NearlyMinimax.ProjectionStatistical


@[expose] public section

open Matrix MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators ENNReal

noncomputable section
namespace NearlyMinimax

/-- The original admissibility norm supplies a genuine cellwise Taylor
approximation, which the actual polynomial design fits exactly. -/
theorem admissible_cell_polynomial_residual_bound {d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (cell : ι → κ) (x : ι → Covariate d) (z : κ → Covariate d)
    (hx : ∀ i, x i ∈ unitCube d) (hz : ∀ c, z c ∈ unitCube d)
    (h : ℝ) (hh : 0 ≤ h) (hradius : ∀ i r, |x i r - z (cell i) r| ≤ h) :
    projectionEnergy
      ((1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := C.order) cell x)) *ᵥ
        (fun i => θ.regression (x i))) ≤
      Fintype.card ι * (taylorErrorFactor C * C.holderBound * h ^ C.smoothness) ^ 2 := by
  classical
  choose P hP using fun c => admissible_regression_taylor_cell C θ hθ (z c) (hz c) h hh
  apply cell_polynomial_residual_bound cell x (fun i => θ.regression (x i)) P
    (fun c => (hP c).1) (taylorErrorFactor C * C.holderBound * h ^ C.smoothness)
  · exact mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
      (Real.rpow_nonneg hh _)
  · intro i
    exact (hP (cell i)).2 (x i) (hx i) (hradius i)

/-- Actual regular-grid polynomial fitting proves the approximation
bound in every smoothness order of the original model. -/
theorem regular_grid_polynomial_residual_bound {d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) (x : ι → Covariate d) (hx : ∀ i, x i ∈ unitCube d) :
    projectionEnergy
      ((1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := C.order)
        (fun i => regularGridCell k hk (x i)) x)) *ᵥ (fun i => θ.regression (x i))) ≤
      Fintype.card ι * (taylorErrorFactor C * C.holderBound * (1 / k) ^ C.smoothness) ^ 2 := by
  apply admissible_cell_polynomial_residual_bound C θ hθ
    (fun i => regularGridCell k hk (x i)) x (regularGridCorner k) hx
    (regular_grid_corner_mem_cube k hk) (1 / k) (by positivity)
  exact fun i r => regular_grid_cell_radius k hk (x i) (hx i) r

/-- The higher-order regular-grid fit leaves sample size minus its
actual rectangular feature count as residual degrees of freedom. -/
theorem regular_grid_polynomial_residual_degrees {d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (ℓ k : ℕ) (hk : 0 < k) (x : ι → Covariate d) :
    (Fintype.card ι : ℝ) - k ^ d * (ℓ + 1 : ℕ) ^ d ≤
      (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ)
        (fun i => regularGridCell k hk (x i)) x)).trace := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    cell_polynomial_residual_degrees (ℓ := ℓ) (fun i => regularGridCell k hk (x i)) x

/-- A genuine Borel higher-order projection estimator on the original
sample space. Features are explicit monomials of observed covariates. -/
def polynomialGridEstimator {d : ℕ} (C : ModelConstants d) (n k : ℕ)
    (hk : 0 < k) : Estimator d n :=
  ⟨fun z => projectionEstimator
    (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := C.order)
      (fun i => regularGridCell k hk (z i).1) (fun i => (z i).1)))
    (fun i => (z i).2), by
    apply empirical_residual_estimator_measurable
    · apply cell_polynomial_design_measurable
      · apply measurable_pi_iff.mpr
        intro i
        exact (regular_grid_cell_measurable k hk).comp (by fun_prop)
      · fun_prop
    · fun_prop⟩

/-- The full-smoothness Taylor bias contribution. -/
def polynomialGridBias {d : ℕ} (C : ModelConstants d) (k : ℕ) : ℝ :=
  4 * (taylorErrorFactor C * C.holderBound * (1 / k) ^ C.smoothness) ^ 4

/-- The conditional full-smoothness projection MSE is proved from the
original Hölder model, explicit features, and actual independent moments. -/
theorem independent_polynomial_grid_projection_mse_bound
    {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2)
    (x : Fin n → Covariate d) (hx : ∀ i, x i ∈ unitCube d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : Fin n → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = θ.variance)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C.fourthBound) :
    (∫ ω, ((polynomialGridEstimator C n k hk).val
      (fun i => (x i, θ.regression (x i) + ε i ω)) - θ.variance) ^ 2 ∂μ) ≤
      gridProjectionConstant C / n + polynomialGridBias C k := by
  let B := cellPolynomialDesign (ℓ := C.order) (fun i => regularGridCell k hk (x i)) x
  have hP := empirical_design_projection_spec B
  have hA := projection_complement _ hP.1 hP.2.1
  have hdegree : (n : ℝ) / 2 ≤ (1 - empiricalDesignProjection B).trace := by
    have hdeg := regular_grid_polynomial_residual_degrees C.order k hk x
    simp only [Fintype.card_fin] at hdeg
    linarith
  have hbound := independent_projection_half_degrees_mse μ _ hA.1 hA.2
    (by simpa using hn) (by simpa using hdegree) (fun i => θ.regression (x i)) ε
    θ.variance C.fourthBound C.holderBound
    (taylorErrorFactor C * C.holderBound * (1 / k) ^ C.smoothness)
    (C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1) C.holderBound_pos.le
    (fun i => admissible_regression_value_bound C θ hθ (x i) (hx i))
    (regular_grid_polynomial_residual_bound C θ hθ k hk x hx)
    hε hind hmean hsecond hfourth
  apply hbound.trans
  have hdiv := div_le_div_of_nonneg_right (admissible_grid_projection_constant_bound C θ hθ)
    (Nat.cast_nonneg n)
  simpa only [Fintype.card_fin, polynomialGridBias] using
    add_le_add hdiv (le_refl (polynomialGridBias C k))


/-- The full-smoothness conditional MSE bound in the extended-real loss
of the actual statistical model, with integrability derived from fourth moments. -/
theorem polynomial_grid_conditional_lintegral_bound
    {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2)
    (x : Fin n → Covariate d) (hx : ∀ i, x i ∈ unitCube d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : Fin n → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = θ.variance)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C.fourthBound) :
    (∫⁻ ω, ENNReal.ofReal (((polynomialGridEstimator C n k hk).val
      (fun i => (x i, θ.regression (x i) + ε i ω)) - θ.variance) ^ 2) ∂μ) ≤
      ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := by
  let B := cellPolynomialDesign (ℓ := C.order) (fun i => regularGridCell k hk (x i)) x
  let A := 1 - empiricalDesignProjection B
  let f := fun i => θ.regression (x i)
  have hP := empirical_design_projection_spec B
  have hA := projection_complement _ hP.1 hP.2.1
  have hX := projection_estimator_memLp_two μ A hA.1 f (fun ω i => ε i ω)
    (fun i => (hε i).mono_exponent (by norm_num))
    (independent_error_product_memLp_two μ ε hε)
  have hsq : Integrable
      (fun ω => (projectionEstimator A (f + fun i => ε i ω) - θ.variance) ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
      (hX.sub (memLp_const θ.variance)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hbound := independent_polynomial_grid_projection_mse_bound C θ hθ k hk hn hcolumns
    x hx μ ε hε hind hmean hsecond hfourth
  change (∫⁻ ω, ENNReal.ofReal
    ((projectionEstimator A (f + fun i => ε i ω) - θ.variance) ^ 2) ∂μ) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hbound

end NearlyMinimax
