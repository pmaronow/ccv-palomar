module

public import RoughRegime.Upper


@[expose] public section

/-!
Matrix spectral ingredients and the inverse-only (`N = 0`) specialization of Lemma 5(a).
The determinant-product case of that lemma is deliberately not claimed here.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial RoughRegime.Upper
namespace RoughRegime.MatrixUpper

/-- The `k`th normalized Chebyshev polynomial on the positive interval. -/
def normalizedChebyshev (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
    (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi)))

lemma normalizedChebyshev_natDegree (lo hi : ℝ) (k : ℕ) :
    (normalizedChebyshev lo hi k).natDegree ≤ k := by
  unfold normalizedChebyshev
  calc
    _ ≤ (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree *
      (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi))).natDegree :=
      natDegree_comp_le
    _ ≤ k * 1 := by
      apply Nat.mul_le_mul
      · simp [Polynomial.Chebyshev.natDegree_T]
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    _ = k := by simp

/-- Polynomial realizing the reciprocal truncation from Lemma 5(a), `ν' = 0`. -/
def scalarReciprocalPolynomial (lo hi : ℝ) (m : ℕ) : ℝ[X] :=
  C (intervalGeometricMean lo hi)⁻¹ *
    (1 + C 2 * ∑ k ∈ Finset.range m,
      C ((-intervalRho lo hi) ^ (k + 1)) * normalizedChebyshev lo hi (k + 1))

lemma scalarReciprocalPolynomial_natDegree (lo hi : ℝ) (m : ℕ) :
    (scalarReciprocalPolynomial lo hi m).natDegree ≤ m := by
  unfold scalarReciprocalPolynomial
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply (natDegree_C_mul_le _ _).trans
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact ((natDegree_C_mul_le _ _).trans
      (normalizedChebyshev_natDegree lo hi (k + 1))).trans
      (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hk))

lemma normalizedChebyshev_eval (lo hi x : ℝ) (k : ℕ) :
    (normalizedChebyshev lo hi k).eval x =
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) := by
  simp [normalizedChebyshev, div_eq_mul_inv, mul_comm]

lemma scalarReciprocalPolynomial_eval (lo hi x : ℝ) (m : ℕ) :
    (scalarReciprocalPolynomial lo hi m).eval x = scalarReciprocalTruncation lo hi m x := by
  simp [scalarReciprocalPolynomial, scalarReciprocalTruncation,
    normalizedChebyshev_eval, Polynomial.eval_finsetSum]

/-- The Chebyshev coefficient has ℓ² operator norm at most one whenever the matrix spectrum
lies in the interval, exactly the spectral bound used before Lemma 5. -/
theorem matrix_chebyshev_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖Polynomial.aeval M (normalizedChebyshev lo hi k)‖ ≤ 1 := by
  have hs : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  rw [← cfc_polynomial _ M hs]
  apply norm_cfc_le (by norm_num)
  intro x hx
  rw [normalizedChebyshev_eval, Real.norm_eq_abs]
  exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt (hSpec hx)) k

/-- Full matrix inverse-only error bound from Lemma 5(a), with a sharper constant.
It holds for arbitrary finite dimensions in the genuine ℓ² operator norm. -/
theorem matrix_inverse_truncation_error {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (m : ℕ) :
    ‖M⁻¹ - Polynomial.aeval M (scalarReciprocalPolynomial lo hi m)‖ ≤
      2 / intervalGeometricMean lo hi * intervalRho lo hi ^ (m + 1) /
        (1 - intervalRho lo hi) := by
  have hs : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hn : ∀ x ∈ spectrum ℝ M, x ≠ 0 := by
    intro x hx
    exact ne_of_gt (hlo.trans_le (hSpec hx).1)
  have hInvCont : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ M) := continuousOn_id.inv₀ hn
  have hInv : cfc (fun x : ℝ => x⁻¹) M = M⁻¹ := by
    have h := cfc_inv (R := ℝ) id M hn continuousOn_id hs
    simp only [id_eq] at h
    have hid : cfc (fun x : ℝ => x) M = M := cfc_id ℝ M hs
    rw [hid, ← Matrix.nonsing_inv_eq_ringInverse] at h
    exact h
  rw [← hInv, ← cfc_polynomial _ M hs,
    ← cfc_sub (fun x : ℝ => x⁻¹) (scalarReciprocalPolynomial lo hi m).eval M hInvCont
      (scalarReciprocalPolynomial lo hi m).continuous.continuousOn]
  have hr : 0 < intervalRho lo hi := intervalRho_pos lo hi hlo hlt
  have hr1 : intervalRho lo hi < 1 := intervalRho_lt_one lo hi hlo hlt
  have hg : 0 < intervalGeometricMean lo hi := by
    unfold intervalGeometricMean
    exact Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt))
  apply norm_cfc_le (by positivity)
  intro x hx
  rw [Real.norm_eq_abs, scalarReciprocalPolynomial_eval]
  exact scalar_reciprocal_truncation_error lo hi x m hlo hlt (hSpec hx)


/-- Matrix whose entries are independent multivariate polynomial variables. -/
def variableMatrix (n : Type*) : Matrix n n (MvPolynomial (n × n) ℝ) :=
  fun i j => MvPolynomial.X (i, j)

lemma variableMatrix_power_degree {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (i j : n) :
    ((variableMatrix n ^ k) i j).totalDegree ≤ k := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro a _
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (ih i a) (by simp [variableMatrix]))

lemma variableMatrix_power_eval {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (k : ℕ) (i j : n) :
    MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2) ((variableMatrix n ^ k) i j) =
      (M ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, map_sum, map_mul, ih]
    simp [variableMatrix]

/-- Explicit entry polynomial for a univariate polynomial in a matrix. -/
def matrixEntryPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : MvPolynomial (n × n) ℝ :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    MvPolynomial.C (q.coeff k) * (variableMatrix n ^ k) i j

lemma matrixEntryPolynomial_degree {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) :
    (matrixEntryPolynomial q i j).totalDegree ≤ q.natDegree := by
  unfold matrixEntryPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc
    _ ≤ (MvPolynomial.C (q.coeff k) : MvPolynomial (n × n) ℝ).totalDegree +
      ((variableMatrix n ^ k) i j).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + k := Nat.add_le_add (by simp) (variableMatrix_power_degree k i j)
    _ ≤ q.natDegree := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)

lemma matrixEntryPolynomial_eval {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (M : Matrix n n ℝ) (i j : n) :
    MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2) (matrixEntryPolynomial q i j) =
      (Polynomial.aeval M q) i j := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [map_sum, map_mul, MvPolynomial.eval_C, variableMatrix_power_eval,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- Entrywise polynomial degree assertion in the inverse-only case of Lemma 5(a). -/
theorem matrix_inverse_truncation_entry_polynomial {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (m : ℕ) (i j : n) :
    ∃ Q : MvPolynomial (n × n) ℝ, Q.totalDegree ≤ m ∧
      ∀ M : Matrix n n ℝ,
        MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2) Q =
          (Polynomial.aeval M (scalarReciprocalPolynomial lo hi m)) i j := by
  refine ⟨matrixEntryPolynomial (scalarReciprocalPolynomial lo hi m) i j, ?_, ?_⟩
  · exact (matrixEntryPolynomial_degree _ i j).trans (scalarReciprocalPolynomial_natDegree lo hi m)
  · intro M
    exact matrixEntryPolynomial_eval _ M i j

end RoughRegime.MatrixUpper
