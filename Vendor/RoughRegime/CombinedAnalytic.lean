module

public import RoughRegime.MatrixKernel
public import RoughRegime.CombinedPolynomial


@[expose] public section

/-! Operator norm and convergence bridge for the full matrix/determinant
combined-index reciprocal truncation of Lemma 5(a). -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace RoughRegime.CombinedAnalytic
open RoughRegime.MatrixDeterminant RoughRegime.MatrixKernel RoughRegime.SeriesBounds
open RoughRegime.Upper RoughRegime.CombinedPolynomial

/-- Convert entrywise scalar formal series to a matrix-valued formal series. -/
def matrixSeries {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n (PowerSeries ℝ)) : PowerSeries (Matrix n n ℝ) :=
  PowerSeries.mk (fun k => coefficientMatrix k K)

lemma matrixSeries_coefficient {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n (PowerSeries ℝ)) (k : ℕ) :
    PowerSeries.coeff k (matrixSeries K) = coefficientMatrix k K := PowerSeries.coeff_mk ..

/-- Entrywise multiplication by a scalar series is matrix multiplication by its scalar matrix. -/
theorem matrixSeries_scalar_mul {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n (PowerSeries ℝ)) (g : PowerSeries ℝ) :
    matrixSeries (fun i j => K i j * g) =
      matrixSeries K * PowerSeries.map (Matrix.scalar n) g := by
  ext k i j
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, PowerSeries.coeff_mul,
    PowerSeries.coeff_map, Matrix.sum_apply, Matrix.scalar_apply, Matrix.mul_diagonal]

/-- Formal coefficients of a product are the actual recursively defined combined indices. -/
theorem addFactors_eq_powerSeries_coeff {R : Type*} [Semiring R]
    (f : PowerSeries R) (gs : List (PowerSeries R)) (k : ℕ) :
    addFactors (fun j => PowerSeries.coeff j f)
      (gs.map (fun g j => PowerSeries.coeff j g)) k =
      PowerSeries.coeff k (f * gs.reverse.prod) := by
  induction gs generalizing k with
  | nil => simp [addFactors]
  | cons g gs ih =>
    simp only [List.map_cons, addFactors, List.reverse_cons, List.prod_append,
      List.prod_singleton]
    rw [← mul_assoc, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij _
    rw [ih]

/-- A scalar coefficient embedded as a scalar matrix has the same operator norm. -/
theorem scalarMatrix_coefficient_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (g : PowerSeries ℝ) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.map (Matrix.scalar n) g)‖ = ‖PowerSeries.coeff k g‖ := by
  rw [PowerSeries.coeff_map]
  exact norm_algebraMap' (Matrix n n ℝ) _

lemma mapped_scalar_prod_reverse {n : Type*} [Fintype n] [DecidableEq n]
    (gs : List (PowerSeries ℝ)) :
    (gs.map (PowerSeries.map (Matrix.scalar n))).reverse.prod =
      PowerSeries.map (Matrix.scalar n) gs.prod := by
  rw [← List.map_reverse, ← map_list_prod, List.prod_reverse]

/-- The genuine matrix/determinant combined generating series. -/
def combinedSeries {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) :
    PowerSeries (Matrix (Fin n0) (Fin n0) ℝ) :=
  matrixSeries (kernelSeries lo hi M0) *
    PowerSeries.map (Matrix.scalar (Fin n0)) (∏ i, (kernelSeries lo hi (M i)).det)

/-- The matrix-valued coefficients evaluate exactly the entry polynomials. -/
theorem combinedSeries_coefficient_entry {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (a b : Fin n0) (k : ℕ) :
    (PowerSeries.coeff k (combinedSeries lo hi M0 M)) a b =
      MvPolynomial.eval (entryValuation M0 M)
        (combinedCoefficientPolynomial n0 dims lo hi a b k) := by
  rw [combinedCoefficientPolynomial_eval]
  rw [combinedSeries, ← matrixSeries_scalar_mul]
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix]

/-- Flatten all reciprocal eigenvalue factors, including zero-dimensional determinant blocks. -/
def eigenvalueSeriesList {N : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) : List (PowerSeries ℝ) :=
  (Finset.univ : Finset ((i : Fin N) × Fin (dims i))).toList.map
    (fun ij => scalarKernelSeries lo hi ((hM ij.1).eigenvalues ij.2))

lemma eigenvalueSeriesList_length {N : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) :
    (eigenvalueSeriesList lo hi M hM).length = ∑ i, dims i := by
  simp only [eigenvalueSeriesList, List.length_map, Finset.length_toList, Finset.card_univ,
    Fintype.card_sigma, Fintype.card_fin]

lemma eigenvalueSeriesList_prod {N : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) :
    (eigenvalueSeriesList lo hi M hM).prod = ∏ i, (kernelSeries lo hi (M i)).det := by
  rw [eigenvalueSeriesList, Finset.prod_map_toList, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  exact (kernelSeries_det_spectral lo hi (M i) (hM i)).symm

/-- The actual combined series coefficients are the Cauchy products of all eigenvalue kernels. -/
theorem combinedSeries_coefficient_eq_addFactors {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (k : ℕ) :
    PowerSeries.coeff k (combinedSeries lo hi M0 M) =
      addFactors (matrixKernelCoefficient lo hi M0)
        ((eigenvalueSeriesList lo hi M hM).map
          (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g))) k := by
  have he := addFactors_eq_powerSeries_coeff (matrixSeries (kernelSeries lo hi M0))
    ((eigenvalueSeriesList lo hi M hM).map (PowerSeries.map (Matrix.scalar (Fin n0)))) k
  rw [mapped_scalar_prod_reverse, eigenvalueSeriesList_prod] at he
  have hf : (fun j => PowerSeries.coeff j (matrixSeries (kernelSeries lo hi M0))) =
      matrixKernelCoefficient lo hi M0 := by
    funext j
    ext a b
    simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, kernelSeries,
      matrixKernelCoefficient]
  rw [hf] at he
  have hg : ((eigenvalueSeriesList lo hi M hM).map
      (PowerSeries.map (Matrix.scalar (Fin n0)))).map (fun g j => PowerSeries.coeff j g) =
      (eigenvalueSeriesList lo hi M hM).map
        (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g)) := by
    rw [List.map_map]
    congr 1
  rw [hg] at he
  exact he.symm

/-- Full factor-count coefficient bound of Lemma 5(a), in the actual operator norm. -/
theorem combinedSeries_coefficient_norm_le {N n0 : ℕ} [Nonempty (Fin n0)] {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ) (hM0 : M0.IsHermitian)
    (hSpec0 : spectrum ℝ M0 ⊆ Set.Icc lo hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi)
    (k : ℕ) :
    ‖PowerSeries.coeff k (combinedSeries lo hi M0 M)‖ ≤
      2 ^ ((∑ i, dims i) + 1) * ((k + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ k := by
  rw [combinedSeries_coefficient_eq_addFactors lo hi M0 M hM]
  have hg : ∀ g ∈ (eigenvalueSeriesList lo hi M hM).map
      (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g)),
      ∀ j, ‖g j‖ ≤ 2 * intervalRho lo hi ^ j := by
    intro g hg j
    rcases List.mem_map.mp hg with ⟨q, hq, rfl⟩
    rcases List.mem_map.mp hq with ⟨ij, _, rfl⟩
    change ‖PowerSeries.coeff j (PowerSeries.map (Matrix.scalar (Fin n0))
      (scalarKernelSeries lo hi ((hM ij.1).eigenvalues ij.2)))‖ ≤ _
    rw [scalarMatrix_coefficient_norm]
    exact scalarKernelSeries_coefficient_norm_le lo hi _ hlo hlt
      (hSpec ij.1 ((hM ij.1).eigenvalues_mem_spectrum_real ij.2)) j
  have hh := addFactors_coefficient_bound (matrixKernelCoefficient lo hi M0)
    ((eigenvalueSeriesList lo hi M hM).map
      (fun g j => (Matrix.scalar (Fin n0)) (PowerSeries.coeff j g)))
    (intervalRho lo hi) 2 2 (intervalRho_pos lo hi hlo hlt) (by norm_num) (by norm_num)
    (matrixKernelCoefficient_norm_le lo hi hlo hlt M0 hM0 hSpec0) hg k
  simpa only [List.length_map, eigenvalueSeriesList_length, pow_succ, mul_assoc,
    mul_left_comm, mul_comm] using hh

/-- Scalar matrices commute with coefficient summation. -/
theorem scalarMatrix_tsum {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℕ → ℝ) (hf : Summable f) :
    (∑' k, (Matrix.scalar n) (f k)) = (Matrix.scalar n) (∑' k, f k) := by
  have hc : Continuous (Matrix.scalar n : ℝ → Matrix n n ℝ) := by
    change Continuous (fun x : ℝ => Matrix.diagonal (fun _ : n => x))
    exact (continuous_pi (fun _ => continuous_id)).matrix_diagonal
  exact (hf.hasSum.map (Matrix.scalar n) hc).tsum_eq

/-- The sum of all determinant factors is the common normalization divided by the determinant product. -/
theorem determinantProduct_tsum {N : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (∏ i, (kernelSeries lo hi (M i)).det)) =
      intervalGeometricMean lo hi ^ (∑ i, dims i) / ∏ i, (M i).det := by
  rw [powerSeries_prod_tsum]
  · simp_rw [kernelSeries_det_tsum lo hi hlo hlt _ (hM _) (hSpec _), Fintype.card_fin]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  · intro i _
    exact kernelSeries_det_summable_norm lo hi hlo hlt (M i) (hM i) (hSpec i)

/-- The actual combined generating series sums to ḡ^(ν'+1) times the inverse/determinant target. -/
theorem combinedSeries_tsum {N n0 : ℕ} [Nonempty (Fin n0)] {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ) (hM0 : M0.IsHermitian)
    (hSpec0 : spectrum ℝ M0 ⊆ Set.Icc lo hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (combinedSeries lo hi M0 M)) =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1) / ∏ i, (M i).det) • M0⁻¹ := by
  let D : PowerSeries ℝ := ∏ i, (kernelSeries lo hi (M i)).det
  have hDn : Summable (fun k => ‖PowerSeries.coeff k D‖) := by
    exact powerSeries_prod_summable_norm Finset.univ _ (fun i _ =>
      kernelSeries_det_summable_norm lo hi hlo hlt (M i) (hM i) (hSpec i))
  have hDmn : Summable (fun k => ‖PowerSeries.coeff k
      (PowerSeries.map (Matrix.scalar (Fin n0)) D)‖) := by
    simpa only [scalarMatrix_coefficient_norm] using hDn
  have hcoef : (fun k => PowerSeries.coeff k (combinedSeries lo hi M0 M)) =
      convolution (matrixKernelCoefficient lo hi M0)
        (fun k => PowerSeries.coeff k (PowerSeries.map (Matrix.scalar (Fin n0)) D)) := by
    funext k
    rw [combinedSeries, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij _
    congr 1
    ext a b
    simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, kernelSeries,
      matrixKernelCoefficient]
  rw [hcoef, convolution_tsum _ _
    (matrixKernelCoefficient_summable_norm lo hi hlo hlt M0 hM0 hSpec0) hDmn,
    matrixKernelCoefficient_tsum lo hi hlo hlt M0 hM0 hSpec0]
  simp only [PowerSeries.coeff_map]
  rw [scalarMatrix_tsum _ hDn.of_norm, determinantProduct_tsum lo hi hlo hlt M hM hSpec,
    Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, smul_smul]
  congr 1
  rw [pow_succ, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Finite matrix polynomial with the exact combined-index truncation and normalization. -/
def truncationMatrix {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (m : ℕ) :
    Matrix (Fin n0) (Fin n0) ℝ :=
  fun a b => MvPolynomial.eval (entryValuation M0 M) (truncationEntryPolynomial n0 dims lo hi a b m)

/-- Exact identification of the concrete entry polynomials with the formal combined-index truncation. -/
theorem truncationMatrix_eq_scaled_sum {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (m : ℕ) :
    truncationMatrix lo hi M0 M m =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ •
        ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (combinedSeries lo hi M0 M) := by
  ext a b
  simp only [truncationMatrix, truncationEntryPolynomial_eval, Matrix.smul_apply,
    smul_eq_mul, Matrix.sum_apply, combinedSeries_coefficient_entry,
    combinedCoefficientPolynomial_eval]

/-- Full Lemma 5(a): the arbitrary determinant-product approximation error in operator norm.
Together with `truncationEntryPolynomial_degree`, this proves the matrix polynomial assertion. -/
theorem matrix_determinant_truncation_error {N n0 : ℕ} [Nonempty (Fin n0)] {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ) (hM0 : M0.IsHermitian)
    (hSpec0 : spectrum ℝ M0 ⊆ Set.Icc lo hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi) (m : ℕ) :
    ‖(∏ i, (M i).det)⁻¹ • M0⁻¹ - truncationMatrix lo hi M0 M m‖ ≤
      2 ^ ((∑ i, dims i) + 1) * (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ *
        ((m + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ k := by
  let ν : ℕ := ∑ i, dims i
  let α : ℝ := (intervalGeometricMean lo hi ^ (ν + 1))⁻¹
  have hg : intervalGeometricMean lo hi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt)))
  have hα : 0 ≤ α := by dsimp [α, intervalGeometricMean]; positivity
  have htarget : (∏ i, (M i).det)⁻¹ • M0⁻¹ =
      α • ∑' k, PowerSeries.coeff k (combinedSeries lo hi M0 M) := by
    rw [combinedSeries_tsum lo hi hlo hlt M0 hM0 hSpec0 M hM hSpec, smul_smul]
    congr 1
    dsimp [α, ν]
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hg), one_mul]
  rw [htarget, truncationMatrix_eq_scaled_sum]
  change ‖α • _ - α • _‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  have he := series_truncation_bound
    (fun k => PowerSeries.coeff k (combinedSeries lo hi M0 M)) ν m (intervalRho lo hi)
    (2 ^ (ν + 1)) (intervalRho_pos lo hi hlo hlt) (intervalRho_lt_one lo hi hlo hlt)
    (by positivity) (combinedSeries_coefficient_norm_le lo hi hlo hlt M0 hM0 hSpec0 M hM hSpec)
  apply (mul_le_mul_of_nonneg_left he hα).trans_eq
  dsimp [α, ν]
  ring

end RoughRegime.CombinedAnalytic
