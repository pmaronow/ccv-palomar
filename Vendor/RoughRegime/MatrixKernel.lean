module

public import RoughRegime.MatrixDeterminant


@[expose] public section

/-!
# Absolute convergence and exact matrix reciprocal kernel sum

All matrices carry the genuine ℓ² operator norm.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial
namespace RoughRegime.MatrixKernel
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant

/-- Matrix coefficient of the normalized reciprocal kernel. -/
def matrixKernelCoefficient {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (k : ℕ) : Matrix n n ℝ :=
  Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)

/-- The matrix coefficients have the paper's geometric operator norm bound. -/
theorem matrixKernelCoefficient_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖matrixKernelCoefficient lo hi M k‖ ≤ 2 * intervalRho lo hi ^ k := by
  have hr := intervalRho_pos lo hi hlo hlt
  have he : matrixKernelCoefficient lo hi M k =
      (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) •
        Polynomial.aeval M (normalizedChebyshev lo hi k) := by
    simp [matrixKernelCoefficient, kernelCoefficientPolynomial, Algebra.smul_def]
  rw [he, norm_smul]
  by_cases hk : k = 0
  · subst k
    simp only [ite_true, norm_one, one_mul, pow_zero]
    exact (matrix_chebyshev_norm_le_one lo hi hlo hlt M hM hSpec 0).trans (by norm_num)
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, abs_neg, abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left
      (matrix_chebyshev_norm_le_one lo hi hlo hlt M hM hSpec k)
      (by positivity : 0 ≤ 2 * intervalRho lo hi ^ k)

/-- Absolute convergence of the genuine matrix coefficient series. -/
theorem matrixKernelCoefficient_summable_norm {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    Summable (fun k => ‖matrixKernelCoefficient lo hi M k‖) := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (matrixKernelCoefficient_norm_le lo hi hlo hlt M hM hSpec)
  exact (summable_geometric_of_lt_one (intervalRho_pos lo hi hlo hlt).le
    (intervalRho_lt_one lo hi hlo hlt)).mul_left (2 : ℝ)

/-- Each matrix coefficient is diagonal in the fixed spectral eigenbasis. -/
theorem matrixKernelCoefficient_spectral {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (hM : M.IsHermitian) (k : ℕ) :
    matrixKernelCoefficient lo hi M k =
      (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => PowerSeries.coeff k (scalarKernelSeries lo hi (hM.eigenvalues i))) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
  have he : matrixKernelCoefficient lo hi M k = coefficientMatrix k (kernelSeries lo hi M) := by
    ext i j
    simp only [matrixKernelCoefficient, coefficientMatrix, kernelSeries, PowerSeries.coeff_mk]
  rw [he, kernelSeries_spectral lo hi M hM, coefficientMatrix_mul_constant,
    coefficientMatrix_constant_mul, coefficientMatrix_diagonal]

/-- The inverse itself has the same spectral representation, with reciprocal eigenvalues. -/
theorem matrix_inverse_spectral {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.IsHermitian) (hn : ∀ i, hM.eigenvalues i ≠ 0) :
    M⁻¹ = (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
  let U : Matrix n n ℝ := hM.eigenvectorUnitary
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.property
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.property
  have hM' : M = U * Matrix.diagonal hM.eigenvalues * star U := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Function.comp_apply,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hM.spectral_theorem
  apply Matrix.inv_eq_left_inv
  change (U * _ * star U) * M = 1
  conv_lhs => arg 2; rw [hM']
  calc
    _ = U * Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹) *
        (star U * U) * Matrix.diagonal hM.eigenvalues * star U := by noncomm_ring
    _ = U * (Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹) *
        Matrix.diagonal hM.eigenvalues) * star U := by rw [hU, mul_one]; noncomm_ring
    _ = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun i => (hM.eigenvalues i)⁻¹ * hM.eigenvalues i) =
          (1 : Matrix n n ℝ) := by
        simp only [inv_mul_cancel₀ (hn _), Matrix.diagonal_one]
      rw [hd, mul_one, hU']

/-- The actual matrix series sums to ḡ M⁻¹. -/
theorem matrixKernelCoefficient_tsum {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    (∑' k, matrixKernelCoefficient lo hi M k) = intervalGeometricMean lo hi • M⁻¹ := by
  let U : Matrix n n ℝ := hM.eigenvectorUnitary
  have hd : Summable (fun k i => PowerSeries.coeff k (scalarKernelSeries lo hi (hM.eigenvalues i))) := by
    rw [Pi.summable]
    intro i
    exact (scalarKernelSeries_summable_norm lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real i))).of_norm
  have hds : (∑' k, fun i => PowerSeries.coeff k (scalarKernelSeries lo hi (hM.eigenvalues i))) =
      fun i => intervalGeometricMean lo hi / hM.eigenvalues i := by
    funext i
    rw [Pi.tsum_apply hd]
    exact scalarKernelSeries_tsum lo hi _ hlo hlt (hSpec (hM.eigenvalues_mem_spectrum_real i))
  have hdmat : Summable (fun k => Matrix.diagonal
      (fun i => PowerSeries.coeff k (scalarKernelSeries lo hi (hM.eigenvalues i)))) := hd.matrix_diagonal
  simp_rw [matrixKernelCoefficient_spectral lo hi M hM]
  rw [(hdmat.mul_left (hM.eigenvectorUnitary : Matrix n n ℝ)).tsum_mul_right,
    hdmat.tsum_mul_left, ← Matrix.diagonal_tsum, hds]
  rw [matrix_inverse_spectral M hM (fun i =>
    ne_of_gt (hlo.trans_le (hSpec (hM.eigenvalues_mem_spectrum_real i)).1))]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  congr 2

end RoughRegime.MatrixKernel
