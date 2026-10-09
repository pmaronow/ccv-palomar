module

public import RoughRegime.MatrixUpper
public import RoughRegime.SeriesBounds


@[expose] public section

/-!
# Determinant coefficients of the matrix reciprocal kernel

The formal determinant series is built from entry polynomials in the actual
matrix variables. Its kth coefficient has total degree at most k.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial

namespace RoughRegime.MatrixDeterminant

open RoughRegime.Upper RoughRegime.MatrixUpper

/-- Degree-compatible products of polynomial-valued power series. -/
theorem coeff_totalDegree_mul_le {V : Type*}
    (f g : PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ k, (PowerSeries.coeff k f).totalDegree ≤ k)
    (hg : ∀ k, (PowerSeries.coeff k g).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (f * g)).totalDegree ≤ k := by
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  exact (MvPolynomial.totalDegree_mul _ _).trans
    ((Nat.add_le_add (hf ij.1) (hg ij.2)).trans_eq
      (Finset.HasAntidiagonal.mem_antidiagonal.mp hij))

/-- Finite products preserve total degree bounded by the series index. -/
theorem coeff_totalDegree_prod_le {V I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ i ∈ s, ∀ k, (PowerSeries.coeff k (f i)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (∏ i ∈ s, f i)).totalDegree ≤ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    apply coeff_totalDegree_mul_le
    · exact hf a (Finset.mem_insert_self ..)
    · intro j
      exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j

/-- Taking a determinant does not increase the total degree of its kth coefficient. -/
theorem determinant_coefficient_totalDegree_le {V n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (PowerSeries (MvPolynomial V ℝ)))
    (hM : ∀ i j k, (PowerSeries.coeff k (M i j)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k M.det).totalDegree ≤ k := by
  rw [Matrix.det_apply, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  simp only [Units.smul_def]
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    (coeff_totalDegree_prod_le Finset.univ (fun i => M (σ i) i) (by
      intro i _
      exact hM (σ i) i) k)

/-- Scalar Chebyshev polynomial giving the kth normalized reciprocal-kernel coefficient. -/
def kernelCoefficientPolynomial (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  C (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) * normalizedChebyshev lo hi k

lemma kernelCoefficientPolynomial_natDegree (lo hi : ℝ) (k : ℕ) :
    (kernelCoefficientPolynomial lo hi k).natDegree ≤ k :=
  (natDegree_C_mul_le _ _).trans (normalizedChebyshev_natDegree lo hi k)

/-- Reciprocal-kernel entry series in independent matrix-entry variables. -/
def variableKernelSeries (lo hi : ℝ) {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix n n (PowerSeries (MvPolynomial (n × n) ℝ)) := fun i j =>
  PowerSeries.mk (fun k => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j)

/-- The determinant coefficient is an actual polynomial in all the matrix entries. -/
def determinantCoefficientPolynomial (lo hi : ℝ) {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) : MvPolynomial (n × n) ℝ :=
  PowerSeries.coeff k (variableKernelSeries lo hi (n := n)).det

theorem determinantCoefficientPolynomial_totalDegree {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (k : ℕ) :
    (determinantCoefficientPolynomial lo hi (n := n) k).totalDegree ≤ k := by
  apply determinant_coefficient_totalDegree_le
  intro i j t
  simp only [variableKernelSeries, PowerSeries.coeff_mk]
  exact (matrixEntryPolynomial_degree _ i j).trans (kernelCoefficientPolynomial_natDegree lo hi t)

/-- The actual matrix kernel as a matrix of formal real power series. -/
def kernelSeries (lo hi : ℝ) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Matrix n n (PowerSeries ℝ) := fun i j =>
  PowerSeries.mk (fun k => (Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)) i j)

/-- Evaluation of all matrix variables produces the actual kernel entry series. -/
theorem variableKernelSeries_map_eval {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) :
    (PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi (n := n)) = kernelSeries lo hi M := by
  ext i j k
  change PowerSeries.coeff k ((PowerSeries.map
    (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2)))
      (PowerSeries.mk (fun t => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi t) i j))) = _
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  change MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2)
    (matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j) = _
  simp only [kernelSeries, PowerSeries.coeff_mk]
  exact matrixEntryPolynomial_eval _ M i j

/-- Each polynomial coefficient evaluates to the kth coefficient of the actual kernel determinant. -/
theorem determinantCoefficientPolynomial_eval {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (k : ℕ) :
    MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2)
      (determinantCoefficientPolynomial lo hi (n := n) k) =
      PowerSeries.coeff k (kernelSeries lo hi M).det := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2)
  have he := congrArg (fun f : PowerSeries ℝ => PowerSeries.coeff k f)
    ((PowerSeries.map φ).map_det (variableKernelSeries lo hi (n := n)))
  rw [variableKernelSeries_map_eval] at he
  rw [PowerSeries.coeff_map] at he
  exact he

/-- Scalar series corresponding to one eigenvalue of the reciprocal kernel. -/
def scalarKernelSeries (lo hi x : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => (kernelCoefficientPolynomial lo hi k).eval x)

private theorem aeval_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (d : n → ℝ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom ℝ) d) q = _
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]
  rfl

def coefficientMatrix {n : Type*} (k : ℕ) (M : Matrix n n (PowerSeries ℝ)) :
    Matrix n n ℝ := fun i j => PowerSeries.coeff k (M i j)

theorem coefficientMatrix_constant_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (M : Matrix n n (PowerSeries ℝ)) (k : ℕ) :
    coefficientMatrix k ((PowerSeries.C.mapMatrix A) * M) = A * coefficientMatrix k M := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_C_mul]

theorem coefficientMatrix_mul_constant {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (M : Matrix n n (PowerSeries ℝ)) (k : ℕ) :
    coefficientMatrix k (M * (PowerSeries.C.mapMatrix A)) = coefficientMatrix k M * A := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul_C]

theorem coefficientMatrix_diagonal {n : Type*} [DecidableEq n]
    (d : n → PowerSeries ℝ) (k : ℕ) :
    coefficientMatrix k (Matrix.diagonal d) = Matrix.diagonal (fun i => PowerSeries.coeff k (d i)) := by
  ext i j
  simp only [coefficientMatrix, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- The actual formal matrix kernel diagonalizes in the same fixed eigenbasis as its argument. -/
theorem kernelSeries_spectral {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    kernelSeries lo hi M =
      (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)) *
      Matrix.diagonal (fun i => scalarKernelSeries lo hi (hM.eigenvalues i)) *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))) := by
  ext i j k
  change (coefficientMatrix k (kernelSeries lo hi M)) i j =
    (coefficientMatrix k (_ * _ * _)) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul, coefficientMatrix_diagonal]
  simp only [coefficientMatrix, kernelSeries, scalarKernelSeries, PowerSeries.coeff_mk]
  have hp := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))
    (kernelCoefficientPolynomial lo hi k)
  rw [← hM.spectral_theorem, aeval_diagonal] at hp
  have hp' : Polynomial.aeval M (kernelCoefficientPolynomial lo hi k) =
      (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => (kernelCoefficientPolynomial lo hi k).eval (hM.eigenvalues i)) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_apply, RCLike.ofReal_real_eq_id,
      id_eq] using hp
  exact congrArg (fun A : Matrix n n ℝ => A i j) hp'

/-- The formal determinant is exactly the product of the scalar eigenvalue reciprocal series. -/
theorem kernelSeries_det_spectral {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    (kernelSeries lo hi M).det = ∏ i, scalarKernelSeries lo hi (hM.eigenvalues i) := by
  rw [kernelSeries_spectral lo hi M hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hu :
      (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul]
    have hunit : (hM.eigenvectorUnitary : Matrix n n ℝ) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
      Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.property
    rw [hunit, map_one, Matrix.det_one]
  calc
    _ = (∏ i, scalarKernelSeries lo hi (hM.eigenvalues i)) *
      ((PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det) := by ring
    _ = _ := by rw [hu, mul_one]

/-- Scalar kernel coefficients have the same geometric bound as in the paper. -/
theorem scalarKernelSeries_coefficient_norm_le (lo hi x : ℝ) (hlo : 0 < lo)
    (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi) (k : ℕ) :
    ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖ ≤ 2 * intervalRho lo hi ^ k := by
  have hr := intervalRho_pos lo hi hlo hlt
  have ht : |(normalizedChebyshev lo hi k).eval x| ≤ 1 := by
    rw [normalizedChebyshev_eval]
    exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt hx) k
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hk : k = 0
  · subst k
    simp [normalizedChebyshev]
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, abs_neg,
      abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * intervalRho lo hi ^ k)

/-- Absolute summability of every scalar eigenvalue kernel. -/
theorem scalarKernelSeries_summable_norm (lo hi x : ℝ) (hlo : 0 < lo)
    (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi) :
    Summable (fun k => ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖) := by
  have hg := (summable_geometric_of_lt_one (intervalRho_pos lo hi hlo hlt).le
    (intervalRho_lt_one lo hi hlo hlt)).mul_left (2 : ℝ)
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (scalarKernelSeries_coefficient_norm_le lo hi x hlo hlt hx) hg

/-- At z=1 the scalar formal kernel sums to the normalized reciprocal. -/
theorem scalarKernelSeries_tsum (lo hi x : ℝ) (hlo : 0 < lo)
    (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (scalarKernelSeries lo hi x)) = intervalGeometricMean lo hi / x := by
  have hs := (scalarKernelSeries_summable_norm lo hi x hlo hlt hx).of_norm
  rw [hs.tsum_eq_zero_add]
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.add_one_ne_zero, ite_false,
    normalizedChebyshev_eval]
  norm_num only [Int.natCast_zero, Polynomial.Chebyshev.T_zero, Polynomial.eval_one,
    ite_true, one_mul]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  exact reciprocal_real_series lo hi x hlo hlt hx

/-- Absolute convergence is stable under the genuine finite Cauchy product. -/
theorem powerSeries_prod_summable_norm {R I : Type*} [NormedCommRing R] [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    Summable (fun k => ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖) := by
  induction s using Finset.induction_on with
  | empty =>
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [PowerSeries.coeff_one, hk]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm
      (hf a (Finset.mem_insert_self ..))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    convert hs using 1
    funext k
    rw [PowerSeries.coeff_mul]

/-- The sum of the coefficients of a finite product is the product of their sums. -/
theorem powerSeries_prod_tsum {R I : Type*} [NormedCommRing R] [CompleteSpace R] [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    (∑' k, PowerSeries.coeff k (∏ i ∈ s, f i)) = ∏ i ∈ s, ∑' k, PowerSeries.coeff k (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [PowerSeries.coeff_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hc : (fun k => PowerSeries.coeff k (f a * ∏ i ∈ s, f i)) =
        RoughRegime.SeriesBounds.convolution
          (fun k => PowerSeries.coeff k (f a))
          (fun k => PowerSeries.coeff k (∏ i ∈ s, f i)) := by
      funext k
      exact PowerSeries.coeff_mul k _ _
    rw [hc, RoughRegime.SeriesBounds.convolution_tsum]
    · rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    · exact hf a (Finset.mem_insert_self ..)
    · exact powerSeries_prod_summable_norm s f
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Absolute convergence of the actual formal determinant coefficients. -/
theorem kernelSeries_det_summable_norm {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    Summable (fun k => ‖PowerSeries.coeff k (kernelSeries lo hi M).det‖) := by
  rw [kernelSeries_det_spectral lo hi M hM]
  apply powerSeries_prod_summable_norm
  intro i _
  exact scalarKernelSeries_summable_norm lo hi _ hlo hlt
    (hSpec (hM.eigenvalues_mem_spectrum_real i))

/-- The actual determinant series sums to the normalized determinant reciprocal. -/
theorem kernelSeries_det_tsum {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (kernelSeries lo hi M).det) =
      intervalGeometricMean lo hi ^ Fintype.card n / M.det := by
  rw [kernelSeries_det_spectral lo hi M hM, powerSeries_prod_tsum]
  · simp_rw [scalarKernelSeries_tsum lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real _))]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
    rw [hM.det_eq_prod_eigenvalues]
    rfl
  · intro i _
    exact scalarKernelSeries_summable_norm lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real i))

/-- The resulting entry-polynomial determinant series is an actual reciprocal determinant series. -/
theorem determinant_reciprocal_series {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) :
    (∑' k, (intervalGeometricMean lo hi ^ Fintype.card n)⁻¹ *
      MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2)
        (determinantCoefficientPolynomial lo hi (n := n) k)) = M.det⁻¹ := by
  simp_rw [determinantCoefficientPolynomial_eval]
  rw [tsum_mul_left, kernelSeries_det_tsum lo hi hlo hlt M hM hSpec]
  have hg : intervalGeometricMean lo hi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt)))
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hg), one_mul]

/-- Uniform combined-index bound for a finite product of geometric scalar series. -/
theorem powerSeries_prod_coefficient_norm_le {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries ℝ) (ρ : ℝ) (hp : 0 < ρ)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ 2 * ρ ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤
      2 ^ s.card * ((k + 1 : ℕ) : ℝ) ^ s.card * ρ ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul, PowerSeries.coeff_one]
    split_ifs with hk
    · subst k
      norm_num
    · simp only [norm_zero]
      positivity
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (fun j => PowerSeries.coeff j (∏ i ∈ s, f i))
      (fun j => PowerSeries.coeff j (f a)) s.card k ρ (2 ^ s.card) 2 hp
      (by positivity) (by norm_num)
      (fun j => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j)
      (hf a (Finset.mem_insert_self ..))
    rw [PowerSeries.coeff_mul]
    simpa only [RoughRegime.SeriesBounds.convolution, Finset.card_insert_of_notMem ha,
      pow_succ] using hh

/-- Determinant coefficients enjoy the combined-index polynomial-geometric bound. -/
theorem kernelSeries_det_coefficient_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖PowerSeries.coeff k (kernelSeries lo hi M).det‖ ≤
      2 ^ Fintype.card n * ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * intervalRho lo hi ^ k := by
  rw [kernelSeries_det_spectral lo hi M hM]
  simpa only [Finset.card_univ] using powerSeries_prod_coefficient_norm_le
    Finset.univ (fun i => scalarKernelSeries lo hi (hM.eigenvalues i))
    (intervalRho lo hi) (intervalRho_pos lo hi hlo hlt)
    (by intro i _ k
        exact scalarKernelSeries_coefficient_norm_le lo hi _ hlo hlt
          (hSpec (hM.eigenvalues_mem_spectrum_real i)) k) k

/-- The finite determinant reciprocal approximation in the actual matrix-entry variables. -/
def determinantReciprocalPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (m : ℕ) : MvPolynomial (n × n) ℝ :=
  MvPolynomial.C ((intervalGeometricMean lo hi ^ Fintype.card n)⁻¹) *
    ∑ k ∈ Finset.range (m + 1), determinantCoefficientPolynomial lo hi (n := n) k

/-- The determinant approximation has total degree at most the combined truncation index. -/
theorem determinantReciprocalPolynomial_totalDegree {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (m : ℕ) :
    (determinantReciprocalPolynomial lo hi (n := n) m).totalDegree ≤ m := by
  unfold determinantReciprocalPolynomial
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  exact (determinantCoefficientPolynomial_totalDegree lo hi k).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- Concrete determinant reciprocal truncation bound, with the actual entry polynomial. -/
theorem determinant_reciprocal_truncation_error {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (m : ℕ) :
    ‖M.det⁻¹ - MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2)
      (determinantReciprocalPolynomial lo hi (n := n) m)‖ ≤
      (intervalGeometricMean lo hi ^ Fintype.card n)⁻¹ * 2 ^ Fintype.card n *
        ((m + 1 : ℕ) : ℝ) ^ Fintype.card n * intervalRho lo hi ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * intervalRho lo hi ^ k := by
  let α := (intervalGeometricMean lo hi ^ Fintype.card n)⁻¹
  have hα : 0 ≤ α := by
    dsimp [α, intervalGeometricMean]
    positivity
  let f : ℕ → ℝ := fun k => α * PowerSeries.coeff k (kernelSeries lo hi M).det
  have hf (k : ℕ) : ‖f k‖ ≤ α * 2 ^ Fintype.card n *
      ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * intervalRho lo hi ^ k := by
    rw [show f k = α * PowerSeries.coeff k (kernelSeries lo hi M).det from rfl,
      norm_mul, Real.norm_eq_abs, abs_of_nonneg hα]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (kernelSeries_det_coefficient_norm_le lo hi hlo hlt M hM hSpec k) hα
  have hsum : (∑' k, f k) = M.det⁻¹ := by
    simpa only [f, α, determinantCoefficientPolynomial_eval] using
      determinant_reciprocal_series lo hi hlo hlt M hM hSpec
  have hfinite : MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2)
      (determinantReciprocalPolynomial lo hi (n := n) m) =
      ∑ k ∈ Finset.range (m + 1), f k := by
    simp only [determinantReciprocalPolynomial, map_mul, map_sum, MvPolynomial.eval_C,
      determinantCoefficientPolynomial_eval, f, α, Finset.mul_sum]
  rw [hfinite, ← hsum]
  exact RoughRegime.SeriesBounds.series_truncation_bound f (Fintype.card n) m
    (intervalRho lo hi) (α * 2 ^ Fintype.card n) (intervalRho_pos lo hi hlo hlt)
    (intervalRho_lt_one lo hi hlo hlt) (by positivity) hf

end RoughRegime.MatrixDeterminant
