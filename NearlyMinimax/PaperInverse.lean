module

public import NearlyMinimax.Chebyshev
public import RoughRegime.CombinedAnalytic


@[expose] public section

/-!
# Reciprocal polynomial ingredients for `upper_B.tex`

The imported algebraic and analytic reciprocal construction is specialized to
one parent determinant, exactly the product in the manuscript. Results stated
with Hermitian matrices below explicitly retain that hypothesis. The scalar
exponent bridge identifies the rate parameter with the manuscript's `τ`.
-/

noncomputable section

namespace NearlyMinimax

open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixUpper

/-- The inverse-series convergence ratio equals `exp(-τ)`. -/
theorem inverse_ratio_exterior_exponent (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    intervalRho a b = Real.exp (-exteriorTau ((a + b) / (b - a))) := by
  exact (exp_neg_exteriorTau a b ha hab).symm

/-- Integer powers of the convergence ratio have the manuscript's exponential form. -/
theorem inverse_ratio_pow (a b : ℝ) (ha : 0 < a) (hab : a < b) (m : ℕ) :
    intervalRho a b ^ m = Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [inverse_ratio_exterior_exponent a b ha hab, ← Real.exp_nat_mul]
  congr 1
  ring

/-- A positive constant independent of truncation degree. -/
def reciprocalErrorConstant (a b : ℝ) : ℝ :=
  2 / intervalGeometricMean a b * intervalRho a b / (1 - intervalRho a b)

theorem reciprocalErrorConstant_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < reciprocalErrorConstant a b := by
  have hr := intervalRho_pos a b ha hab
  have hr1 := intervalRho_lt_one a b ha hab
  have hg : 0 < intervalGeometricMean a b :=
    Real.sqrt_pos.mpr (mul_pos ha (ha.trans hab))
  unfold reciprocalErrorConstant
  positivity

/-- The scalar reciprocal admits a degree-`m` polynomial with error `C exp(-mτ)`. -/
theorem scalar_inverse_polynomial (a b : ℝ) (ha : 0 < a) (hab : a < b) (m : ℕ) :
    ∃ P : ℝ[X], P.natDegree ≤ m ∧
      ∀ x ∈ Set.Icc a b, |x⁻¹ - P.eval x| ≤
        reciprocalErrorConstant a b *
          Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  refine ⟨scalarReciprocalPolynomial a b m, scalarReciprocalPolynomial_natDegree a b m, ?_⟩
  intro x hx
  rw [scalarReciprocalPolynomial_eval]
  apply (scalar_reciprocal_truncation_error a b x m ha hab hx).trans_eq
  rw [pow_succ, inverse_ratio_pow a b ha hab m]
  unfold reciprocalErrorConstant
  ring

/-- The same exponential reciprocal bound holds in the genuine matrix operator norm. -/
theorem matrix_inverse_polynomial_error {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) (m : ℕ) :
    ‖A⁻¹ - Polynomial.aeval A (scalarReciprocalPolynomial a b m)‖ ≤
      reciprocalErrorConstant a b *
        Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  apply (matrix_inverse_truncation_error a b ha hab A hA hSpec m).trans_eq
  rw [pow_succ, inverse_ratio_pow a b ha hab m]
  unfold reciprocalErrorConstant
  ring

open RoughRegime.CombinedPolynomial RoughRegime.CombinedAnalytic

/-- The entry-variable type for the current matrix and its single parent. -/
abbrev parentInverseVariables (r : ℕ) := Variables r (fun _ : Fin 1 => r)

/-- Exact free-entry polynomial implementing the manuscript's single-parent truncation. -/
def parentInverseEntryPolynomial (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    MvPolynomial (parentInverseVariables r) ℝ :=
  truncationEntryPolynomial r (fun _ : Fin 1 => r) a b i j m

/-- Evaluating the free-entry polynomials gives `P_m(A,C)`. -/
def parentInversePolynomial {r : ℕ} (a b : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  truncationMatrix a b A (fun _ : Fin 1 => C) m

/-- Degree at most `m` is proved in all the free current and parent matrix entries. -/
theorem parentInverseEntryPolynomial_degree (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    (parentInverseEntryPolynomial a b r m i j).totalDegree ≤ m :=
  truncationEntryPolynomial_degree r (fun _ : Fin 1 => r) a b i j m

/-- The concrete matrix is evaluation of its entry polynomials for arbitrary matrices. -/
theorem parentInversePolynomial_eval {r : ℕ} (a b : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) (i j : Fin r) :
    parentInversePolynomial a b A C m i j =
      MvPolynomial.eval (entryValuation A (fun _ : Fin 1 => C))
        (parentInverseEntryPolynomial a b r m i j) := rfl

/-- A finite positive constant independent of matrix entries and truncation degree. -/
def parentInverseErrorConstant (a b : ℝ) (r : ℕ) : ℝ :=
  2 ^ (r + 1) * (intervalGeometricMean a b ^ (r + 1))⁻¹ *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k

theorem parentInverseErrorConstant_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (r : ℕ) :
    0 < parentInverseErrorConstant a b r := by
  have hr := intervalRho_pos a b ha hab
  have hr1 := intervalRho_lt_one a b ha hab
  have hg : 0 < intervalGeometricMean a b :=
    Real.sqrt_pos.mpr (mul_pos ha (ha.trans hab))
  have hs := RoughRegime.SeriesBounds.weighted_geometric_summable r (intervalRho a b) hr hr1
  have ht : 0 < ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k := by
    apply hs.tsum_pos (fun k => by positivity) 0
    simp
  unfold parentInverseErrorConstant
  positivity

/-- The inverse/determinant approximation bound of (U4-approx), for symmetric spectral matrices. -/
theorem parent_inverse_polynomial_error {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b) (m : ℕ) :
    ‖C.det⁻¹ • A⁻¹ - parentInversePolynomial a b A C m‖ ≤
      parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have h := matrix_determinant_truncation_error (N := 1) (dims := fun _ : Fin 1 => r)
    a b ha hab A hA hSpecA (fun _ : Fin 1 => C) (fun _ => hC) (fun _ => hSpecC) m
  simp only [Fin.sum_univ_one, Fin.prod_univ_one] at h
  apply h.trans_eq
  rw [inverse_ratio_pow a b ha hab m]
  unfold parentInverseErrorConstant
  ring

/-- Scalar-matrix conjugation as an algebra homomorphism. -/
def matrixSimilarity {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℝ where
  toFun A := (Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp

/-- Every matrix polynomial commutes with similarity. -/
theorem aeval_matrixSimilarity {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) (P : ℝ[X]) :
    Polynomial.aeval (matrixSimilarity Q A) P = matrixSimilarity Q (Polynomial.aeval A P) := by
  exact Polynomial.aeval_algHom_apply (matrixSimilarity Q) A P

/-- The operator norm under similarity gains only its condition-number factor. -/
theorem matrixSimilarity_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    ‖matrixSimilarity Q A‖ ≤ ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ * ‖A‖ := by
  calc
    _ ≤ ‖(Q : Matrix n n ℝ) * A‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ := norm_mul_le _ _
    _ ≤ (‖(Q : Matrix n n ℝ)‖ * ‖A‖) * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

/-- Matrix inversion commutes with similarity, including singular matrices. -/
theorem matrixSimilarity_inv {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    (matrixSimilarity Q A)⁻¹ = matrixSimilarity Q A⁻¹ := by
  change ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ))⁻¹ =
    (Q : Matrix n n ℝ) * A⁻¹ * (↑Q⁻¹ : Matrix n n ℝ)
  simp only [Matrix.mul_inv_rev, ← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc]

/-- The inverse-polynomial bound for matrices similar to a symmetric spectral matrix. -/
theorem matrix_inverse_similar_error {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) (Q : (Matrix n n ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ ≤ χ) (m : ℕ) :
    ‖(matrixSimilarity Q A)⁻¹ -
      Polynomial.aeval (matrixSimilarity Q A) (scalarReciprocalPolynomial a b m)‖ ≤
        χ * reciprocalErrorConstant a b *
          Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [matrixSimilarity_inv, aeval_matrixSimilarity, ← map_sub]
  have hχ0 : 0 ≤ χ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  apply (matrixSimilarity_norm_le Q _).trans
  apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (matrix_inverse_polynomial_error a b ha hab A hA hSpec m) hχ0).trans_eq
  ring

open RoughRegime.MatrixDeterminant

private theorem kernelSeries_coefficient {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℝ) (k : ℕ) :
    coefficientMatrix k (kernelSeries a b A) =
      Polynomial.aeval A (kernelCoefficientPolynomial a b k) := by
  ext i j
  simp only [coefficientMatrix, kernelSeries, PowerSeries.coeff_mk]

/-- The reciprocal kernel formal series commutes with arbitrary invertible similarity. -/
theorem kernelSeries_matrixSimilarity {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    kernelSeries a b (matrixSimilarity Q A) =
      PowerSeries.C.mapMatrix (Q : Matrix n n ℝ) * kernelSeries a b A *
        PowerSeries.C.mapMatrix (↑Q⁻¹ : Matrix n n ℝ) := by
  ext i j k
  change (coefficientMatrix k (kernelSeries a b (matrixSimilarity Q A))) i j =
    (coefficientMatrix k (_ * _ * _)) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul]
  rw [kernelSeries_coefficient, kernelSeries_coefficient]
  exact congrArg (fun M : Matrix n n ℝ => M i j)
    (aeval_matrixSimilarity Q A (kernelCoefficientPolynomial a b k))

/-- The parent reciprocal determinant formal series is similarity invariant. -/
theorem kernelSeries_det_matrixSimilarity {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    (kernelSeries a b (matrixSimilarity Q A)).det = (kernelSeries a b A).det := by
  rw [kernelSeries_matrixSimilarity]
  have h := Matrix.det_units_conj
    (Units.map (PowerSeries.C.mapMatrix : Matrix n n ℝ →+* Matrix n n (PowerSeries ℝ)).toMonoidHom Q)
    (kernelSeries a b A)
  simpa using h

private theorem matrixSeries_kernel_matrixSimilarity {r : ℕ}
    (a b : ℝ) (Q : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A : Matrix (Fin r) (Fin r) ℝ) :
    matrixSeries (kernelSeries a b (matrixSimilarity Q A)) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (matrixSeries (kernelSeries a b A)) := by
  apply PowerSeries.ext
  intro k
  rw [matrixSeries_coefficient, PowerSeries.coeff_map, matrixSeries_coefficient,
    kernelSeries_coefficient, kernelSeries_coefficient]
  exact aeval_matrixSimilarity Q A (kernelCoefficientPolynomial a b k)

private theorem matrixSimilarity_scalar {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (x : ℝ) :
    matrixSimilarity Q (Matrix.scalar n x) = Matrix.scalar n x := by
  exact (matrixSimilarity Q).commutes x

private theorem combinedSeries_parent_matrixSimilarity {r : ℕ}
    (a b : ℝ) (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A C : Matrix (Fin r) (Fin r) ℝ) :
    combinedSeries a b (matrixSimilarity Q A) (fun _ : Fin 1 => matrixSimilarity R C) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (combinedSeries a b A (fun _ : Fin 1 => C)) := by
  rw [combinedSeries, combinedSeries, map_mul]
  rw [matrixSeries_kernel_matrixSimilarity]
  simp only [Fin.prod_univ_one, kernelSeries_det_matrixSimilarity]
  congr 1
  apply PowerSeries.ext
  intro k
  simp only [PowerSeries.coeff_map]
  change Matrix.scalar (Fin r) _ = matrixSimilarity Q (Matrix.scalar (Fin r) _)
  exact (matrixSimilarity_scalar Q _).symm

/-- The single-parent truncation is equivariant in the current matrix and invariant in the parent. -/
theorem parentInversePolynomial_matrixSimilarity {r : ℕ}
    (a b : ℝ) (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) :
    parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m =
      matrixSimilarity Q (parentInversePolynomial a b A C m) := by
  rw [parentInversePolynomial, parentInversePolynomial,
    truncationMatrix_eq_scaled_sum, truncationMatrix_eq_scaled_sum]
  simp_rw [combinedSeries_parent_matrixSimilarity, PowerSeries.coeff_map]
  rw [map_smul, map_sum]
  rfl

/-- (U4-approx) for arbitrary matrices similar to symmetric spectral matrices, with condition gain `χ`. -/
theorem parent_inverse_similar_error {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (m : ℕ) :
    ‖(matrixSimilarity R C).det⁻¹ • (matrixSimilarity Q A)⁻¹ -
      parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m‖ ≤
        χ * parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
          Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have hdet : (matrixSimilarity R C).det = C.det := Matrix.det_units_conj R C
  rw [hdet, matrixSimilarity_inv, parentInversePolynomial_matrixSimilarity, ← map_smul, ← map_sub]
  have hχ0 : 0 ≤ χ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  apply (matrixSimilarity_norm_le Q _).trans
  apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (parent_inverse_polynomial_error a b ha hab A C hA hC hSpecA hSpecC m) hχ0).trans_eq
  ring

/-- The determinant-cleared fitted increment numerator from (Udef-increment). -/
def incrementNumerator {n : Type*} [Fintype n] [DecidableEq n]
    (G C T : Matrix n n ℝ) (β βminus : n → ℝ) : n → ℝ :=
  C.det • β - G.mulVec (T.mulVec (C.adjugate.mulVec βminus))

/-- The adjugate identity proves (U5-identity) for every invertible current and parent matrix. -/
theorem incrementNumerator_identity {n : Type*} [Fintype n] [DecidableEq n]
    (G C T : Matrix n n ℝ) (hG : G.det ≠ 0) (hC : C.det ≠ 0) (β βminus : n → ℝ) :
    C.det⁻¹ • G⁻¹.mulVec (incrementNumerator G C T β βminus) =
      G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus) := by
  have hunitG : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  rw [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hunitG, Matrix.one_mulVec,
    smul_sub, smul_smul, inv_mul_cancel₀ hC, one_smul]
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, Matrix.mulVec_smul]

/-- The cleared numerator preserves the increment cancellation before approximation. -/
theorem incrementNumerator_factorization {n : Type*} [Fintype n] [DecidableEq n]
    (G C T : Matrix n n ℝ) (hG : G.det ≠ 0) (hC : C.det ≠ 0) (β βminus : n → ℝ) :
    incrementNumerator G C T β βminus =
      C.det • G.mulVec (G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus)) := by
  have hunitG : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hid := incrementNumerator_identity G C T hG hC β βminus
  have h := congrArg (fun v : n → ℝ => C.det • G.mulVec v) hid
  simpa only [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hC, one_smul,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunitG, Matrix.one_mulVec] using h

/-- Positive-interval spectrum proves nonzero determinant, without an invertibility hypothesis. -/
theorem spectral_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (ha : 0 < a) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : A.det ≠ 0 := by
  rw [hA.det_eq_prod_eigenvalues]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact ne_of_gt (ha.trans_le (hSpec (hA.eigenvalues_mem_spectrum_real i)).1)

/-- A Hermitian matrix with positive interval spectrum has operator norm at most the upper endpoint. -/
theorem spectral_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : ‖A‖ ≤ b := by
  have hs : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  rw [← cfc_id ℝ A hs]
  apply norm_cfc_le (by linarith)
  intro x hx
  have h := hSpec hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.le.trans h.1)] using h.2

/-- The determinant of a positive spectral matrix is bounded by the endpoint to the dimension. -/
theorem spectral_det_abs_le {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : |A.det| ≤ b ^ Fintype.card n := by
  rw [hA.det_eq_prod_eigenvalues, Finset.abs_prod]
  calc
    ∏ i, |hA.eigenvalues i| ≤ ∏ _i : n, b := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact abs_nonneg _
      · intro i hi
        have h := hSpec (hA.eigenvalues_mem_spectrum_real i)
        rw [abs_of_nonneg (ha.le.trans h.1)]
        exact h.2
    _ = _ := by simp

/-- Determinant clearing preserves the small increment with the precise spectral-size factor. -/
theorem increment_numerator_norm_le {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (β βminus : Fin r → ℝ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (incrementNumerator G Cminus T β βminus)‖ ≤
      χ * b ^ (r + 1) * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
        (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus))‖ := by
  dsimp only
  let G := matrixSimilarity Q A
  let Cminus := matrixSimilarity R C
  let δ := G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)
  have hG : G.det ≠ 0 := by
    rw [show G.det = A.det from Matrix.det_units_conj Q A]
    exact spectral_det_ne_zero a b ha A hA hSpecA
  have hCm : Cminus.det ≠ 0 := by
    rw [show Cminus.det = C.det from Matrix.det_units_conj R C]
    exact spectral_det_ne_zero a b ha C hC hSpecC
  have hχ0 : 0 ≤ χ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  have hb : 0 < b := ha.trans hab
  have hnG : ‖G‖ ≤ χ * b := by
    apply (matrixSimilarity_norm_le Q A).trans
    apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg A)).trans
    exact mul_le_mul_of_nonneg_left (spectral_norm_le a b ha hab A hA hSpecA) hχ0
  have hdC : |Cminus.det| ≤ b ^ r := by
    rw [show Cminus.det = C.det from Matrix.det_units_conj R C]
    simpa using spectral_det_abs_le a b ha hab C hC hSpecC
  change ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (incrementNumerator G Cminus T β βminus)‖ ≤ _
  rw [incrementNumerator_factorization G Cminus T hG hCm]
  change ‖Cminus.det • (EuclideanSpace.equiv (Fin r) ℝ).symm (G.mulVec δ)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  have hv := G.l2_opNorm_mulVec ((EuclideanSpace.equiv (Fin r) ℝ).symm δ)
  calc
    |Cminus.det| * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (G.mulVec δ)‖ ≤
        b ^ r * (‖G‖ * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm δ‖) :=
      mul_le_mul hdC hv (norm_nonneg _) (by positivity)
    _ ≤ b ^ r * ((χ * b) * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm δ‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnG (norm_nonneg _)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Applying any inverse/determinant approximation to the cleared numerator incurs only
its operator error times the numerator norm. This is the analytic step behind (U5-error). -/
theorem increment_polynomial_error {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (β βminus : Fin r → ℝ) (m : ℕ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    let N := incrementNumerator G Cminus T β βminus
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((parentInversePolynomial a b G Cminus m).mulVec N -
        (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)))‖ ≤
      (χ * parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a)))) *
        ‖(EuclideanSpace.equiv (Fin r) ℝ).symm N‖ := by
  dsimp only
  let G := matrixSimilarity Q A
  let Cminus := matrixSimilarity R C
  let N := incrementNumerator G Cminus T β βminus
  have hG : G.det ≠ 0 := by
    rw [show G.det = A.det from Matrix.det_units_conj Q A]
    exact spectral_det_ne_zero a b ha A hA hSpecA
  have hCm : Cminus.det ≠ 0 := by
    rw [show Cminus.det = C.det from Matrix.det_units_conj R C]
    exact spectral_det_ne_zero a b ha C hC hSpecC
  have hid := incrementNumerator_identity G Cminus T hG hCm β βminus
  change ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
    ((parentInversePolynomial a b G Cminus m).mulVec N -
      (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)))‖ ≤ _
  rw [← hid, ← Matrix.smul_mulVec, ← Matrix.sub_mulVec]
  have hn := (parentInversePolynomial a b G Cminus m - Cminus.det⁻¹ • G⁻¹).l2_opNorm_mulVec
    ((EuclideanSpace.equiv (Fin r) ℝ).symm N)
  apply hn.trans
  rw [norm_sub_rev]
  exact mul_le_mul_of_nonneg_right
    (parent_inverse_similar_error a b ha hab A C hA hC hSpecA hSpecC Q R χ hχ m)
    (norm_nonneg _)

end NearlyMinimax
