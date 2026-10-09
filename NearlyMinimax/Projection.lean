module

public import Mathlib


@[expose] public section

/-!
# Residual projection algebra

The deterministic matrix identities and expectation calculation behind
Lemma `projection-upper`.  These statements permit rank deficient design
matrices: only the symmetric idempotent residual matrix is required.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

/-- Squared Euclidean length, independent of the sup norm on function spaces. -/
def projectionEnergy {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := x ⬝ᵥ x

/-- The residual quadratic numerator. -/
def projectionQuadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

/-- The residual variance estimator before clipping. -/
def projectionEstimator {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  projectionQuadratic A x / A.trace

theorem projectionEnergy_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ projectionEnergy x := by
  unfold projectionEnergy dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- Idempotence saves a degrees-of-freedom factor in the quadratic variance. -/
theorem projection_trace_square {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A * A = A) : (A * A).trace = A.trace := by
  rw [hA]

/-- The Frobenius square of a symmetric projection equals its trace. -/
theorem projection_sum_squares_eq_trace {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A) :
    (∑ i, ∑ j, A i j ^ 2) = A.trace := by
  calc
    (∑ i, ∑ j, A i j ^ 2) = (A * A).trace := by
      unfold trace diag
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_apply]
      apply Finset.sum_congr rfl
      intro j hj
      have hs : A j i = A i j := congrArg (fun M : Matrix ι ι ℝ => M i j) hsym
      rw [hs, pow_two]
    _ = A.trace := by rw [hidem]

/-- For a symmetric idempotent matrix, the quadratic form is precisely
the residual's squared Euclidean length. -/
theorem projection_quadratic_eq_energy {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A) (f : ι → ℝ) :
    projectionQuadratic A f = projectionEnergy (A *ᵥ f) := by
  unfold projectionQuadratic projectionEnergy
  symm
  rw [dotProduct_mulVec, ← mulVec_transpose, hsym, mulVec_mulVec, hidem, dotProduct_comm]

/-- The residual and fitted components are orthogonal. -/
theorem projection_orthogonal {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A) (f : ι → ℝ) :
    (A *ᵥ f) ⬝ᵥ (f - A *ᵥ f) = 0 := by
  rw [dotProduct_sub]
  have h := projection_quadratic_eq_energy A hsym hidem f
  unfold projectionQuadratic projectionEnergy at h
  rw [dotProduct_comm (A *ᵥ f) f, h, sub_self]

/-- A symmetric projection cannot increase Euclidean length. -/
theorem projection_energy_le {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A) (f : ι → ℝ) :
    projectionEnergy (A *ᵥ f) ≤ projectionEnergy f := by
  have horth := projection_orthogonal A hsym hidem f
  have hpos := projectionEnergy_nonneg (f - A *ᵥ f)
  have hdecomp : projectionEnergy f = projectionEnergy (A *ᵥ f) +
      projectionEnergy (f - A *ᵥ f) := by
    have hid : f = A *ᵥ f + (f - A *ᵥ f) := by abel
    conv_lhs => rw [hid]
    unfold projectionEnergy
    rw [dotProduct_add, add_dotProduct, add_dotProduct, horth,
      dotProduct_comm (f - A *ᵥ f) (A *ᵥ f), horth]
    ring
  linarith

/-- Any candidate fitted vector killed by the residual projection gives
an upper bound for the residual approximation error. -/
theorem projection_residual_minimality {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
    (f q : ι → ℝ) (hq : A *ᵥ q = 0) :
    projectionEnergy (A *ᵥ f) ≤ projectionEnergy (f - q) := by
  have hAq : A *ᵥ (f - q) = A *ᵥ f := by rw [mulVec_sub, hq, sub_zero]
  rw [← hAq]
  exact projection_energy_le A hsym hidem (f - q)

/-- A pointwise polynomial approximation of size `b` bounds the total
residual squared error by the sample size multiplied by `b²`. -/
theorem projection_approximation_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
    (f q : ι → ℝ) (hq : A *ᵥ q = 0) (b : ℝ) (hb : 0 ≤ b)
    (happrox : ∀ i, |f i - q i| ≤ b) :
    projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * b ^ 2 := by
  apply (projection_residual_minimality A hsym hidem f q hq).trans
  unfold projectionEnergy dotProduct
  calc
    (∑ i, (f - q) i * (f - q) i) ≤ ∑ _i : ι, b ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hs := (sq_le_sq₀ (abs_nonneg _) hb).mpr (happrox i)
      rw [sq_abs] at hs
      simpa only [Pi.sub_apply, pow_two] using hs
    _ = _ := by simp

/-- Quadratic expansion separates approximation bias, the linear noise
term, and the centered noise quadratic form. -/
theorem projection_quadratic_add {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (f ε : ι → ℝ) :
    projectionQuadratic A (f + ε) = projectionQuadratic A f +
      2 * ((A *ᵥ f) ⬝ᵥ ε) + projectionQuadratic A ε := by
  unfold projectionQuadratic
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  have hcross : f ⬝ᵥ (A *ᵥ ε) = (A *ᵥ f) ⬝ᵥ ε := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
  rw [hcross, dotProduct_comm ε (A *ᵥ f)]
  ring

/-- Entrywise expansion of the actual quadratic form. -/
theorem projection_quadratic_sum {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    projectionQuadratic A x = ∑ i, ∑ j, A i j * x i * x j := by
  unfold projectionQuadratic mulVec dotProduct
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Finite quadratic noise forms are integrable under coordinate `L²` bounds. -/
theorem projection_quadratic_integrable {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ) :
    Integrable (fun ω => projectionQuadratic A (ε ω)) μ := by
  simp_rw [projection_quadratic_sum]
  apply integrable_finset_sum
  intro i hi
  apply integrable_finset_sum
  intro j hj
  convert ((hε i).integrable_mul (hε j)).const_mul (A i j) using 1
  funext ω
  simp [mul_assoc]

/-- The expected noise quadratic form is variance times trace.  The
hypothesis gives ordinary coordinate second moments, not a conclusion
about the quadratic form. -/
theorem projection_noise_expectation {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (V : ℝ) (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0) :
    (∫ ω, projectionQuadratic A (ε ω) ∂μ) = V * A.trace := by
  have hij (i j : ι) : Integrable (fun ω => A i j * ε ω i * ε ω j) μ := by
    convert ((hε i).integrable_mul (hε j)).const_mul (A i j) using 1
    funext ω
    simp [mul_assoc]
  simp_rw [projection_quadratic_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum _ (fun j _ => hij i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hij _ j), mul_assoc,
    integral_const_mul, hcov, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold trace diag
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Centered coordinate noise has zero expectation in every linear form. -/
theorem projection_linear_noise_expectation {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ι → ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0) :
    (∫ ω, x ⬝ᵥ ε ω ∂μ) = 0 := by
  unfold dotProduct
  rw [integral_finset_sum Finset.univ (fun i _ =>
    ((hε i).integrable (by norm_num)).const_mul (x i))]
  simp_rw [integral_const_mul, hmean, mul_zero]
  simp

/-- The residual estimator's conditional expectation is variance plus
squared approximation residual divided by the degrees of freedom. -/
theorem projection_estimator_expectation {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
    (hd : A.trace ≠ 0) (f : ι → ℝ) (ε : Ω → ι → ℝ) (V : ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hcov : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0) :
    (∫ ω, projectionEstimator A (f + ε ω) ∂μ) =
      V + projectionEnergy (A *ᵥ f) / A.trace := by
  have hlin : Integrable (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) μ := by
    unfold dotProduct
    apply integrable_finset_sum
    intro i hi
    exact ((hε i).integrable (by norm_num)).const_mul ((A *ᵥ f) i)
  have hquad := projection_quadratic_integrable μ A ε hε
  have hsum : Integrable (fun ω => projectionQuadratic A f + 2 * ((A *ᵥ f) ⬝ᵥ ε ω)) μ :=
    (integrable_const (projectionQuadratic A f)).add (hlin.const_mul 2)
  simp_rw [projectionEstimator, projection_quadratic_add A hsym f]
  rw [integral_div, integral_add hsum hquad,
    integral_add (integrable_const (projectionQuadratic A f)) (hlin.const_mul 2), integral_const,
    probReal_univ, one_smul, integral_const_mul,
    projection_linear_noise_expectation μ (A *ᵥ f) ε hε hmean,
    mul_zero, add_zero, projection_noise_expectation μ A ε V hε hcov,
    projection_quadratic_eq_energy A hsym hidem f]
  field_simp
  ring

/-- Independence and centered errors imply the coordinate covariance
identities used by the quadratic expectation theorem. -/
theorem projection_coordinate_covariance {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → ι → ℝ) (V : ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hind : iIndepFun (fun i ω => ε ω i) μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, (ε ω i) ^ 2 ∂μ) = V) :
    ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [← pow_two]
    exact hsecond i
  · simp only [if_neg hij]
    have hi := (hind.indepFun hij).integral_mul_eq_mul_integral
      (hε i).aestronglyMeasurable (hε j).aestronglyMeasurable
    simpa only [Pi.mul_apply, hmean, mul_zero] using hi

/-- A linear noise form has second moment variance multiplied by the
squared Euclidean length of its coefficient vector. -/
theorem projection_linear_noise_second_moment {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (x : ι → ℝ) (ε : Ω → ι → ℝ)
    (V : ℝ) (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0) :
    (∫ ω, (x ⬝ᵥ ε ω) ^ 2 ∂μ) = V * projectionEnergy x := by
  have hid (v : ι → ℝ) : projectionQuadratic (vecMulVec x x) v = (x ⬝ᵥ v) ^ 2 := by
    unfold projectionQuadratic
    rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_comm v x]
    simp only [smul_eq_mul, pow_two]
  have he := projection_noise_expectation μ (vecMulVec x x) ε V hε hcov
  simp_rw [hid] at he
  simpa only [trace_vecMulVec, projectionEnergy] using he

/-- Fourth moments of the coordinate errors guarantee square
integrability of any finite quadratic form. -/
theorem projection_quadratic_memLp_two {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 4 μ) :
    MemLp (fun ω => projectionQuadratic A (ε ω)) 2 μ := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  simp_rw [projection_quadratic_sum]
  apply memLp_finset_sum
  intro i hi
  apply memLp_finset_sum
  intro j hj
  have hprod : MemLp (fun ω => ε ω i * ε ω j) 2 μ := by
    convert (hε j).mul (r := 2) (hε i) using 1
    funext ω
    simp [mul_comm]
  simpa only [mul_assoc] using hprod.const_mul (A i j)

/-- Bias–variance decomposition for an estimator under a probability law. -/
theorem projection_mse_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (V : ℝ)
    (hX : MemLp X 2 μ) :
    (∫ ω, (X ω - V) ^ 2 ∂μ) = variance X μ + ((∫ ω, X ω ∂μ) - V) ^ 2 := by
  have hvar := variance_eq_sub (hX.sub (memLp_const V))
  change variance (fun ω => X ω - V) μ =
    (∫ ω, (X ω - V) ^ 2 ∂μ) - (∫ ω, X ω - V ∂μ) ^ 2 at hvar
  have hmean : (∫ ω, X ω - V ∂μ) = (∫ ω, X ω ∂μ) - V := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const V)]
    simp
  rw [variance_sub_const hX.aestronglyMeasurable V, hmean] at hvar
  linarith

/-- The actual residual variance estimator has MSE equal to its variance
plus squared approximation bias; square integrability is proved from
fourth moments and the expectation from independent centered errors. -/
theorem projection_estimator_mse {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
    (hd : A.trace ≠ 0) (f : ι → ℝ) (ε : Ω → ι → ℝ) (V : ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 4 μ)
    (hind : iIndepFun (fun i ω => ε ω i) μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, (ε ω i) ^ 2 ∂μ) = V) :
    (∫ ω, (projectionEstimator A (f + ε ω) - V) ^ 2 ∂μ) =
      variance (fun ω => projectionEstimator A (f + ε ω)) μ +
        (projectionEnergy (A *ᵥ f) / A.trace) ^ 2 := by
  have hεtwo (i : ι) : MemLp (fun ω => ε ω i) 2 μ := (hε i).mono_exponent (by norm_num)
  have hshift (i : ι) : MemLp (fun ω => (f + ε ω) i) 4 μ := by
    exact (memLp_const (f i)).add (hε i)
  have hquad := projection_quadratic_memLp_two μ A (fun ω => f + ε ω) hshift
  have hest : MemLp (fun ω => projectionEstimator A (f + ε ω)) 2 μ := by
    simpa only [projectionEstimator, div_eq_mul_inv, mul_comm] using hquad.const_mul A.trace⁻¹
  rw [projection_mse_decomposition μ _ V hest,
    projection_estimator_expectation μ A hsym hidem hd f ε V hεtwo hmean
      (projection_coordinate_covariance μ ε V hεtwo hind hmean hsecond)]
  ring

/-- An idempotent real matrix has trace equal to the dimension of its
range, including all rank deficient cases. -/
theorem projection_trace_eq_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hidem : A * A = A) : A.trace = A.rank := by
  have hi : IsIdempotentElem A.mulVecLin := by
    change A.mulVecLin ∘ₗ A.mulVecLin = A.mulVecLin
    rw [← mulVecLin_mul, hidem]
  have hp := (LinearMap.isProj_range_iff_isIdempotentElem A.mulVecLin).mpr hi
  have ht := hp.trace
  change LinearMap.trace ℝ (ι → ℝ) A.mulVecLin = (A.rank : ℝ) at ht
  rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] at ht
  exact ht

/-- A fit whose range is contained in the design-column range consumes
at most one degree of freedom per design column. -/
theorem projection_degrees_of_freedom_bound {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (P : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hidem : P * P = P)
    (hrange : LinearMap.range P.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    (Fintype.card ι : ℝ) - Fintype.card κ ≤ (1 - P).trace := by
  have hr : P.rank ≤ Fintype.card κ :=
    (Submodule.finrank_mono hrange).trans B.rank_le_card_width
  have hrreal : (P.rank : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  rw [trace_sub, trace_one, projection_trace_eq_rank P hidem]
  linarith

/-- The complementary residual of a symmetric idempotent fit is itself
symmetric and idempotent. -/
theorem projection_complement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P) :
    (1 - P)ᵀ = 1 - P ∧ (1 - P) * (1 - P) = 1 - P := by
  constructor
  · rw [transpose_sub, transpose_one, hsym]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hidem]
    abel

/-- Expanding a quadratic-form variance against the coordinate product
covariances gives the usual diagonal-plus-off-diagonal formula.  The
covariance hypotheses are the primitive four-coordinate moment rules
that independent centered errors satisfy. -/
theorem projection_quadratic_variance_from_product_covariances
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (ε : Ω → ι → ℝ) (V : ℝ) (c : ι → ℝ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : ∀ i j k l,
      covariance (fun ω => ε ω i * ε ω j) (fun ω => ε ω k * ε ω l) μ =
        (if i = k ∧ j = l then (if i = j then c i else V ^ 2) else 0) +
        (if i = l ∧ j = k ∧ i ≠ j then V ^ 2 else 0)) :
    variance (fun ω => projectionQuadratic A (ε ω)) μ =
      ∑ i, ∑ j, A i j ^ 2 * (if i = j then c i else 2 * V ^ 2) := by
  have hexp : (fun ω => projectionQuadratic A (ε ω)) =
      (fun ω => ∑ p : ι × ι, A p.1 p.2 * (ε ω p.1 * ε ω p.2)) := by
    funext ω
    rw [Fintype.sum_prod_type, projection_quadratic_sum]
    simp only [mul_assoc]
  rw [hexp, variance_fun_sum (fun (p : ι × ι) => (hproducts p.1 p.2).const_mul (A p.1 p.2))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fintype.sum_prod_type]
  have hs : A j i = A i j := congrArg (fun M : Matrix ι ι ℝ => M i j) hsym
  simp only [ite_and, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hs]
  by_cases hij : i = j
  · simp [hij, Finset.sum_ite_irrel, Finset.sum_ite_eq, pow_two]
    ring
  · simp [hij, Finset.sum_ite_irrel, Finset.sum_ite_eq, pow_two]
    ring

/-- The diagonal-plus-off-diagonal variance is bounded by a constant
multiplied by the trace of a residual projection. -/
theorem projection_quadratic_variance_bound
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (ε : Ω → ι → ℝ)
    (V C : ℝ) (c : ι → ℝ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : ∀ i j k l,
      covariance (fun ω => ε ω i * ε ω j) (fun ω => ε ω k * ε ω l) μ =
        (if i = k ∧ j = l then (if i = j then c i else V ^ 2) else 0) +
        (if i = l ∧ j = k ∧ i ≠ j then V ^ 2 else 0))
    (hc : ∀ i, c i ≤ C) (hV : 2 * V ^ 2 ≤ C) :
    variance (fun ω => projectionQuadratic A (ε ω)) μ ≤ C * A.trace := by
  rw [projection_quadratic_variance_from_product_covariances μ A hsym ε V c hproducts hcov,
    ← projection_sum_squares_eq_trace A hsym hidem, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hb : (if i = j then c i else 2 * V ^ 2) ≤ C := by
    split_ifs
    · exact hc i
    · exact hV
  nlinarith [sq_nonneg (A i j)]

/-- The elementary variance-of-a-sum estimate follows from nonnegativity
of the variance of the difference; no independence between the two
quadratic-estimator terms is needed. -/
theorem projection_variance_add_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun ω => X ω + Y ω) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
  have hn := variance_nonneg (fun ω => X ω - Y ω) μ
  rw [variance_fun_sub hX hY] at hn
  rw [variance_fun_add hX hY]
  linarith

/-- Square integrability of every coordinate product suffices for
square integrability of the noise quadratic form. -/
theorem projection_quadratic_memLp_two_of_products {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ) :
    MemLp (fun ω => projectionQuadratic A (ε ω)) 2 μ := by
  simp_rw [projection_quadratic_sum]
  apply memLp_finset_sum
  intro i hi
  apply memLp_finset_sum
  intro j hj
  simpa only [mul_assoc] using (hproducts i j).const_mul (A i j)

/-- Combining the quadratic and linear noise terms proves the variance
bound for the actual residual estimator from coordinate second moments
and product covariance identities. -/
theorem projection_estimator_variance_bound
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hd : 0 < A.trace)
    (f : ι → ℝ) (ε : Ω → ι → ℝ) (V C : ℝ) (c : ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : ∀ i j k l,
      covariance (fun ω => ε ω i * ε ω j) (fun ω => ε ω k * ε ω l) μ =
        (if i = k ∧ j = l then (if i = j then c i else V ^ 2) else 0) +
        (if i = l ∧ j = k ∧ i ≠ j then V ^ 2 else 0))
    (hc : ∀ i, c i ≤ C) (hV : 2 * V ^ 2 ≤ C) :
    variance (fun ω => projectionEstimator A (f + ε ω)) μ ≤
      (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 := by
  have hlin : MemLp (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) 2 μ := by
    unfold dotProduct
    exact memLp_finset_sum Finset.univ (fun i _ => (hε i).const_mul ((A *ᵥ f) i))
  have hquad := projection_quadratic_memLp_two_of_products μ A ε hproducts
  have hlinvar : variance (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) μ =
      V * projectionEnergy (A *ᵥ f) := by
    rw [variance_of_integral_eq_zero hlin.aemeasurable
      (projection_linear_noise_expectation μ (A *ᵥ f) ε hε hmean)]
    exact projection_linear_noise_second_moment μ (A *ᵥ f) ε V hε hsecond
  have hnum := projection_variance_add_le μ
    (fun ω => 2 * ((A *ᵥ f) ⬝ᵥ ε ω)) (fun ω => projectionQuadratic A (ε ω))
    (hlin.const_mul 2) hquad
  rw [variance_const_mul, hlinvar] at hnum
  have hqbound := projection_quadratic_variance_bound μ A hsym hidem ε V C c
    hproducts hcov hc hV
  have hsum : MemLp (fun ω => 2 * ((A *ᵥ f) ⬝ᵥ ε ω) + projectionQuadratic A (ε ω)) 2 μ :=
    (hlin.const_mul 2).add hquad
  have hvar : variance (fun ω => projectionEstimator A (f + ε ω)) μ =
      A.trace⁻¹ ^ 2 * variance
        (fun ω => 2 * ((A *ᵥ f) ⬝ᵥ ε ω) + projectionQuadratic A (ε ω)) μ := by
    simp_rw [projectionEstimator, projection_quadratic_add A hsym f, add_assoc,
      div_eq_mul_inv, mul_comm _ A.trace⁻¹]
    rw [variance_const_mul, variance_const_add hsum.aestronglyMeasurable]
  rw [hvar]
  have hcomb : variance (fun ω => 2 * ((A *ᵥ f) ⬝ᵥ ε ω) + projectionQuadratic A (ε ω)) μ ≤
      2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f) := by
    nlinarith [hnum, hqbound]
  calc
    _ ≤ A.trace⁻¹ ^ 2 * (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) :=
      mul_le_mul_of_nonneg_left hcomb (sq_pos_of_pos (inv_pos.mpr hd)).le
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring

/-- The response residual quadratic estimator is square integrable under
coordinate and coordinate-product `L²` assumptions. -/
theorem projection_estimator_memLp_two {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (f : ι → ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ) :
    MemLp (fun ω => projectionEstimator A (f + ε ω)) 2 μ := by
  have hlin : MemLp (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) 2 μ := by
    unfold dotProduct
    exact memLp_finset_sum Finset.univ (fun i _ => (hε i).const_mul ((A *ᵥ f) i))
  have hquad := projection_quadratic_memLp_two_of_products μ A ε hproducts
  have hsum : MemLp (fun ω => projectionQuadratic A f +
      2 * ((A *ᵥ f) ⬝ᵥ ε ω) + projectionQuadratic A (ε ω)) 2 μ :=
    ((memLp_const (projectionQuadratic A f)).add (hlin.const_mul 2)).add hquad
  simpa only [projectionEstimator, projection_quadratic_add A hsym f,
    div_eq_mul_inv, mul_comm] using hsum.const_mul A.trace⁻¹

/-- The conditional residual-projection risk bound, proved from
coordinate moments, product covariance rules, and the actual estimator.
The deterministic approximation theorem can now bound the displayed
residual energy uniformly over irregular designs. -/
theorem projection_estimator_mse_bound
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hd : 0 < A.trace)
    (f : ι → ℝ) (ε : Ω → ι → ℝ) (V C : ℝ) (c : ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : ∀ i j k l,
      covariance (fun ω => ε ω i * ε ω j) (fun ω => ε ω k * ε ω l) μ =
        (if i = k ∧ j = l then (if i = j then c i else V ^ 2) else 0) +
        (if i = l ∧ j = k ∧ i ≠ j then V ^ 2 else 0))
    (hc : ∀ i, c i ≤ C) (hV : 2 * V ^ 2 ≤ C) :
    (∫ ω, (projectionEstimator A (f + ε ω) - V) ^ 2 ∂μ) ≤
      (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 +
        (projectionEnergy (A *ᵥ f) / A.trace) ^ 2 := by
  rw [projection_mse_decomposition μ _ V
    (projection_estimator_memLp_two μ A hsym f ε hε hproducts),
    projection_estimator_expectation μ A hsym hidem hd.ne' f ε V hε hmean hsecond,
    add_sub_cancel_left]
  exact add_le_add
    (projection_estimator_variance_bound μ A hsym hidem hd f ε V C c hε hmean hsecond
      hproducts hcov hc hV) le_rfl

end NearlyMinimax
