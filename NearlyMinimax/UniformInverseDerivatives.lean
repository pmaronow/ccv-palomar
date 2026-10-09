module

public import NearlyMinimax.PaperIncrement
public import RoughRegime.ComplexDerivativeBridge


@[expose] public section

/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/

noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial

section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]

def matrixChebyshevT (x : R) (n : ℕ) : R := aeval x (Chebyshev.T ℝ (n : ℤ))
def matrixChebyshevU (x : R) (n : ℤ) : R := aeval x (Chebyshev.U ℝ n)

theorem matrixChebyshevT_recurrence (x : R) (n : ℕ) :
    matrixChebyshevT x (n + 2) = 2 * x * matrixChebyshevT x (n + 1) - matrixChebyshevT x n := by
  unfold matrixChebyshevT
  rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega, Chebyshev.T_add_two]
  simp [map_ofNat]

theorem matrixChebyshevU_recurrence (x : R) (n : ℤ) :
    matrixChebyshevU x (n + 1) = 2 * x * matrixChebyshevU x n - matrixChebyshevU x (n - 1) := by
  unfold matrixChebyshevU
  rw [Chebyshev.U_add_one]
  simp [map_ofNat]

/-- The forcing term for Chebyshev polynomials at two possibly noncommuting matrices. -/
def chebyshevForcing (x y : R) (j : ℕ) : R :=
  if j = 0 then y - x else 2 * (y - x) * matrixChebyshevT y j

def chebyshevResponse (x : R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) - 1 - j) * f j

theorem chebyshevResponse_recurrence (x : R) (f : ℕ → R) (n : ℕ) :
    chebyshevResponse x f (n + 2) =
      2 * x * chebyshevResponse x f (n + 1) - chebyshevResponse x f n + f (n + 1) := by
  unfold chebyshevResponse
  push_cast
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  simp only [show (n : ℤ) + 2 - 1 - n = 1 by ring,
    show (n : ℤ) + 2 - 1 - (n + 1) = 0 by ring,
    show (n : ℤ) + 1 - 1 - n = 0 by ring]
  simp only [matrixChebyshevU, Chebyshev.U_zero, Chebyshev.U_one,
    map_one, map_mul, map_ofNat, aeval_X, one_mul]
  change (∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) + 2 - 1 - j) * f j) +
    2 * x * f n + f (n + 1) =
    2 * x * ((∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) + 1 - 1 - j) * f j) + f n) -
      ∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) - 1 - j) * f j + f (n + 1)
  have hindex (j : ℕ) : (n : ℤ) + 2 - 1 - j = ((n : ℤ) + 1 - 1 - j) + 1 := by ring
  simp_rw [hindex, matrixChebyshevU_recurrence]
  have hindex' (j : ℕ) : (n : ℤ) + 1 - 1 - j - 1 = (n : ℤ) - 1 - j := by ring
  simp_rw [hindex']
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  noncomm_ring

/-- Exact discrete variation of constants; no commutativity of the two arguments is assumed. -/
theorem matrixChebyshevT_perturbation_identity (x y : R) (n : ℕ) :
    matrixChebyshevT y n - matrixChebyshevT x n =
      chebyshevResponse x (chebyshevForcing x y) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevT, chebyshevResponse]
  | one => simp [matrixChebyshevT, chebyshevResponse, chebyshevForcing, matrixChebyshevU]
  | more n hn hn1 =>
    rw [matrixChebyshevT_recurrence, matrixChebyshevT_recurrence,
      chebyshevResponse_recurrence, ← hn, ← hn1]
    simp only [chebyshevForcing, show n + 1 ≠ 0 by omega, ↓reduceIte]
    noncomm_ring

end ChebyshevPerturbation

/-- A finite positive weighted geometric constant; it is independent of polynomial degree. -/
def perturbationConstant (η : ℝ) : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * η ^ k

theorem perturbationConstant_pos (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    0 < perturbationConstant η := by
  have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * η ^ k) := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  unfold perturbationConstant
  apply hs.tsum_pos (fun k => by positivity) 0
  simp

theorem weighted_convolution_le_constant (η : ℝ) (hη : 0 < η) (hη1 : η < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * η ^ (n - j)) ≤ perturbationConstant η := by
  have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * η ^ k) := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  rw [← Finset.sum_range_reflect]
  have he (j : ℕ) (hj : j ∈ Finset.range n) : n - (n - 1 - j) = j + 1 := by
    have := Finset.mem_range.mp hj
    omega
  calc
    _ = ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * η ^ (j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j hj]
    _ ≤ ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * η ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [pow_succ]
      calc
        _ = (((j + 1 : ℕ) : ℝ) * η ^ j) * η := by ring
        _ ≤ (((j + 1 : ℕ) : ℝ) * η ^ j) * 1 :=
          mul_le_mul_of_nonneg_left hη1.le (by positivity)
        _ = _ := by ring
    _ ≤ _ := hs.sum_le_tsum (Finset.range n) (fun k hk => by positivity)

/-- Discrete Gronwall majorant with a second-order convolution kernel. -/
theorem recurrence_exponential_majorant (u : ℕ → ℝ) (η δ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hu : ∀ n, u n ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * u j) (n : ℕ) :
    η ^ n * u n ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
        η ^ n * (((n - j : ℕ) : ℝ) * u j) ≤
          2 * (((n - j : ℕ) : ℝ) * η ^ (n - j)) := by
      have hjn := Finset.mem_range.mp hj
      have hp : η ^ n = η ^ (n - j) * η ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hjn)]
      calc
        _ = (((n - j : ℕ) : ℝ) * η ^ (n - j)) * (η ^ j * u j) := by rw [hp]; ring
        _ ≤ (((n - j : ℕ) : ℝ) * η ^ (n - j)) * 2 :=
          mul_le_mul_of_nonneg_left (ih j hjn) (by positivity)
        _ = _ := by ring
    have hsum := Finset.sum_le_sum hterm
    have hpow : η ^ n ≤ 1 := pow_le_one₀ hη.le hη1.le
    calc
      η ^ n * u n ≤ η ^ n * (1 + 2 * δ * ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * u j) :=
        mul_le_mul_of_nonneg_left (hu n) (pow_nonneg hη.le n)
      _ = η ^ n + 2 * δ * ∑ j ∈ Finset.range n,
          η ^ n * (((n - j : ℕ) : ℝ) * u j) := by rw [← Finset.mul_sum]; ring
      _ ≤ 1 + 2 * δ * ∑ j ∈ Finset.range n,
          2 * (((n - j : ℕ) : ℝ) * η ^ (n - j)) :=
        add_le_add hpow (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = 1 + 4 * δ * ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * η ^ (n - j) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ 1 + 4 * δ * perturbationConstant η :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left
          (weighted_convolution_le_constant η hη hη1 n) (show (0 : ℝ) ≤ 4 * δ by positivity))
      _ ≤ 2 := by linarith

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]

private theorem norm_two_ring : ‖(2 : R)‖ = 2 := by
  have h : (2 : R) = (2 : ℝ) • (1 : R) := by norm_num [Algebra.smul_def, map_ofNat]
  rw [h, norm_smul, norm_one, Real.norm_two, mul_one]

theorem matrixChebyshevU_norm_le (x : R) (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (n : ℕ) :
    ‖matrixChebyshevU x (n : ℤ)‖ ≤ (n : ℝ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevU]
  | one =>
    have hx1 : ‖x‖ ≤ 1 := by simpa [matrixChebyshevT] using hx 1
    simp only [matrixChebyshevU, Nat.cast_one, Chebyshev.U_one, map_mul, map_ofNat, aeval_X]
    calc
      _ ≤ ‖(2 : R)‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ 2 := by rw [norm_two_ring]; linarith
      _ = _ := by norm_num
  | more n hn hn1 =>
    have he : matrixChebyshevU x ((n + 2 : ℕ) : ℤ) =
        2 * matrixChebyshevT x (n + 2) + matrixChebyshevU x (n : ℤ) := by
      unfold matrixChebyshevU matrixChebyshevT
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega, Chebyshev.U_eq_two_mul_T_add_U]
      simp [map_ofNat]
    rw [he]
    calc
      _ ≤ ‖2 * matrixChebyshevT x (n + 2)‖ + ‖matrixChebyshevU x (n : ℤ)‖ := norm_add_le _ _
      _ ≤ 2 * ‖matrixChebyshevT x (n + 2)‖ + ((n : ℝ) + 1) := by
        exact add_le_add (by simpa only [norm_two_ring] using norm_mul_le (2 : R) _) hn
      _ ≤ _ := by have h := hx (n + 2); push_cast; linarith

theorem chebyshevForcing_norm_le (x y : R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ‖y - x‖ ≤ δ) (j : ℕ) :
    ‖chebyshevForcing x y j‖ ≤ 2 * δ * ‖matrixChebyshevT y j‖ := by
  unfold chebyshevForcing
  split_ifs with hj
  · subst j
    simpa [matrixChebyshevT] using hd.trans (show δ ≤ 2 * δ by linarith)
  · calc
      _ ≤ ‖(2 : R) * (y - x)‖ * ‖matrixChebyshevT y j‖ := norm_mul_le _ _
      _ ≤ (2 * δ) * ‖matrixChebyshevT y j‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_mul_le _ _).trans (by rw [norm_two_ring]; gcongr)

theorem matrixChebyshevT_norm_volterra (x y : R)
    (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ‖y - x‖ ≤ δ) (n : ℕ) :
    ‖matrixChebyshevT y n‖ ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖ := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖matrixChebyshevU x ((n : ℤ) - 1 - j) * chebyshevForcing x y j‖ ≤
        2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) := by
    have hjn := Finset.mem_range.mp hj
    have hi : (n : ℤ) - 1 - j = ((n - 1 - j : ℕ) : ℤ) := by omega
    have hn : ((n - 1 - j : ℕ) : ℝ) + 1 = ((n - j : ℕ) : ℝ) := by
      exact_mod_cast (show n - 1 - j + 1 = n - j by omega)
    rw [hi]
    calc
      _ ≤ ‖matrixChebyshevU x ((n - 1 - j : ℕ) : ℤ)‖ *
          ‖chebyshevForcing x y j‖ := norm_mul_le _ _
      _ ≤ (((n - 1 - j : ℕ) : ℝ) + 1) *
          (2 * δ * ‖matrixChebyshevT y j‖) :=
        mul_le_mul (matrixChebyshevU_norm_le x hx _) (chebyshevForcing_norm_le x y δ hδ hd j)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [hn]; ring
  have he : matrixChebyshevT y n = matrixChebyshevT x n +
      chebyshevResponse x (chebyshevForcing x y) n := by
    have h := matrixChebyshevT_perturbation_identity x y n
    exact sub_eq_iff_eq_add'.mp h
  rw [he]
  calc
    _ ≤ ‖matrixChebyshevT x n‖ + ‖chebyshevResponse x (chebyshevForcing x y) n‖ := norm_add_le _ _
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        ‖matrixChebyshevU x ((n : ℤ) - 1 - j) * chebyshevForcing x y j‖ :=
      add_le_add (hx n) (norm_sum_le _ _)
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) :=
      add_le_add (le_refl 1) (Finset.sum_le_sum hterm)
    _ = _ := by rw [Finset.mul_sum]

/-- Uniform exponential control in a fixed noncommutative neighborhood of a bounded
Chebyshev center. The radius depends on `η`, never on the polynomial degree. -/
theorem matrixChebyshevT_neighborhood_bound (x y : R)
    (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (η δ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1) (hd : ‖y - x‖ ≤ δ) (n : ℕ) :
    η ^ n * ‖matrixChebyshevT y n‖ ≤ 2 :=
  recurrence_exponential_majorant (fun n => ‖matrixChebyshevT y n‖) η δ hη hη1 hδ hsmall
    (matrixChebyshevT_norm_volterra x y hx δ hδ hd) n

end ChebyshevNorm

section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

/-- Finite Cauchy products preserve a common geometric envelope in any normed
commutative ring, including the complexified matrix entries. -/
theorem powerSeries_prod_geometric_bound (s : Finset I) (f : I → PowerSeries R)
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤
      B ^ s.card * ((k + 1 : ℕ) : ℝ) ^ s.card * q ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul, PowerSeries.coeff_one]
    split_ifs with hk
    · subst k; simp
    · simp only [norm_zero]; positivity
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (fun j => PowerSeries.coeff j (∏ i ∈ s, f i))
      (fun j => PowerSeries.coeff j (f a)) s.card k q (B ^ s.card) B hq
      (by positivity) hB
      (fun j => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j)
      (hf a (Finset.mem_insert_self ..))
    rw [PowerSeries.coeff_mul]
    simpa only [RoughRegime.SeriesBounds.convolution, Finset.card_insert_of_notMem ha,
      pow_succ] using hh

end PowerSeriesBounds

section ComplexMatrices
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def normalizeMatrix (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)

theorem normalizedChebyshev_aeval_complex (lo hi : ℝ) (A : Matrix n n ℂ) (k : ℕ) :
    aeval A (normalizedChebyshev lo hi k) = matrixChebyshevT (normalizeMatrix lo hi A) k := by
  rw [normalizedChebyshev, aeval_comp]
  congr 1
  simp [normalizeMatrix, Algebra.smul_def]

theorem normalizedChebyshev_complex_center_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖matrixChebyshevT (normalizeMatrix lo hi A) k‖ ≤ 1 := by
  rw [← normalizedChebyshev_aeval_complex]
  have hs : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  rw [← cfc_polynomial _ A hs]
  apply norm_cfc_le (by norm_num)
  intro x hx
  rw [normalizedChebyshev_eval, Real.norm_eq_abs]
  exact RoughRegime.Upper.chebyshev_abs_le_one _
    (interval_argument_mem lo hi x hlo hlt (hSpec hx)) k

theorem normalizeMatrix_sub (lo hi : ℝ) (A B : Matrix n n ℂ) :
    normalizeMatrix lo hi B - normalizeMatrix lo hi A =
      (intervalHalfWidth lo hi)⁻¹ • (B - A) := by
  simp only [normalizeMatrix, ← smul_sub]
  congr 1
  abel

theorem matrix_entry_norm_le_l2 (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
  have hi := PiLp.norm_apply_le (T e) i
  have hentry : (T e) i = A i j := by
    simp [T, e, Matrix.toEuclideanCLM_toLp, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  rw [hentry] at hi
  exact hi.trans (by simpa [he, T, Matrix.l2_opNorm_toEuclideanCLM] using
    (T.le_opNorm e))

/-- The complex kernel is evaluated at arbitrary, possibly nonnormal matrices. -/
def complexKernelSeries (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun k => (aeval A (kernelCoefficientPolynomial lo hi k)) i j)

theorem complex_kernel_coefficient_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      4 * (intervalRho lo hi / η) ^ k := by
  have hb := matrixChebyshevT_neighborhood_bound
    (normalizeMatrix lo hi A) (normalizeMatrix lo hi B)
    (normalizedChebyshev_complex_center_bound lo hi hlo hlt A hA hSpec)
    η δ hη hη1 hδ hsmall hd k
  unfold kernelCoefficientPolynomial
  rw [map_mul, aeval_C, ← Algebra.smul_def, norm_smul, normalizedChebyshev_aeval_complex]
  have hηk : 0 < η ^ k := pow_pos hη k
  have hr := intervalRho_pos lo hi hlo hlt
  split_ifs with hk
  · subst k
    simp [matrixChebyshevT]
  · rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num,
      abs_pow, abs_neg, abs_of_pos hr]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hηk).mpr
    calc
      _ = 2 * intervalRho lo hi ^ k * (η ^ k * ‖matrixChebyshevT (normalizeMatrix lo hi B) k‖) := by ring
      _ ≤ 2 * intervalRho lo hi ^ k * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

theorem complex_kernel_entry_coefficient_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ)
    (i j : n) (k : ℕ) :
    ‖PowerSeries.coeff k (complexKernelSeries lo hi B i j)‖ ≤
      4 * (intervalRho lo hi / η) ^ k := by
  simp only [complexKernelSeries, PowerSeries.coeff_mk]
  exact (matrix_entry_norm_le_l2 _ i j).trans
    (complex_kernel_coefficient_bound lo hi hlo hlt A B hA hSpec η δ hη hη1 hδ hsmall hd k)

theorem determinant_series_coefficient_bound (K : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k K.det‖ ≤
      (Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n *
        ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
  have hsign (σ : Equiv.Perm n) (P : PowerSeries ℂ) :
      ‖PowerSeries.coeff k (Equiv.Perm.sign σ • P)‖ = ‖PowerSeries.coeff k P‖ := by
    obtain hs | hs := Int.units_eq_one_or (Equiv.Perm.sign σ)
    · rw [hs]; simp
    · rw [hs]; simp [Units.smul_def]
  rw [Matrix.det_apply, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (Equiv.Perm.sign σ • ∏ i, K (σ i) i)‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (∏ i, K (σ i) i)‖ := by
      apply Finset.sum_congr rfl; intro σ hσ; exact hsign σ _
    _ ≤ ∑ _σ : Equiv.Perm n,
        B ^ Fintype.card n * ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa using powerSeries_prod_geometric_bound Finset.univ (fun i => K (σ i) i) q B hq hB
        (fun i hi => hK _ _ ) k
    _ = _ := by simp [mul_assoc]

/-- A finite combined-index inverse/determinant truncation admits a common
degree-independent bound whenever its entries share a geometric envelope. -/
theorem combined_truncation_uniform_bound (K L : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hq1 : q < 1) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k)
    (hL : ∀ i j k, ‖PowerSeries.coeff k (L i j)‖ ≤ B * q ^ k)
    (i j : n) (m : ℕ) :
    ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (K i j * L.det)‖ ≤
      ((Fintype.card (Equiv.Perm n) : ℝ) * B ^ (Fintype.card n + 1)) *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k := by
  let A : ℝ := (Fintype.card (Equiv.Perm n) : ℝ) * B ^ (Fintype.card n + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoeff (k : ℕ) : ‖PowerSeries.coeff k (K i j * L.det)‖ ≤
      A * ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k := by
    rw [mul_comm, PowerSeries.coeff_mul]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (fun k => PowerSeries.coeff k L.det) (fun k => PowerSeries.coeff k (K i j))
      (Fintype.card n) k q ((Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n) B
      hq (by positivity) hB (determinant_series_coefficient_bound L q B hq hB hL) (hK i j)
    simpa [RoughRegime.SeriesBounds.convolution, A, pow_succ, mul_assoc] using hh
  have hs := (RoughRegime.SeriesBounds.weighted_geometric_summable (Fintype.card n + 1) q hq hq1).mul_left A
  calc
    _ ≤ ∑ k ∈ Finset.range (m + 1), ‖PowerSeries.coeff k (K i j * L.det)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), A * ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k :=
      Finset.sum_le_sum (fun k hk => hcoeff k)
    _ ≤ ∑' k : ℕ, A * (((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k) := by
      simpa only [mul_assoc] using hs.sum_le_tsum (Finset.range (m + 1)) (fun k hk => by positivity)
    _ = _ := by rw [tsum_mul_left]

theorem variableMatrix_power_eval_complex (A : Matrix n n ℂ) (k : ℕ) (i j : n) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun ij : n × n => A ij.1 ij.2)
      ((variableMatrix n ^ k) i j) = (A ^ k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> simp
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, ih]
    simp [variableMatrix]

theorem matrixEntryPolynomial_eval_complex (p : ℝ[X]) (A : Matrix n n ℂ) (i j : n) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun ij : n × n => A ij.1 ij.2)
      (matrixEntryPolynomial p i j) = (aeval A p) i j := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    variableMatrix_power_eval_complex, Matrix.sum_apply, Matrix.smul_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  rfl

theorem variableKernelSeries_eval_complex (lo hi : ℝ) (A : Matrix n n ℂ) :
    (PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun ij : n × n => A ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi (n := n)) = complexKernelSeries lo hi A := by
  ext i j k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, PowerSeries.coeff_map]
  simp only [variableKernelSeries, complexKernelSeries, PowerSeries.coeff_mk]
  exact matrixEntryPolynomial_eval_complex _ A i j

/-- Complexification of real matrices preserves the real functional calculus. -/
def ofRealMatrixStarAlgHom : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Complex.ofRealHom.mapMatrix with
    commutes' := by
      intro a
      ext i j
      change ((if i = j then a else 0 : ℝ) : ℂ) = if i = j then (a : ℂ) else 0
      split_ifs <;> simp
    map_star' := by
      intro A
      ext i j
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] }

theorem ofRealMatrixStarAlgHom_injective : Function.Injective (ofRealMatrixStarAlgHom (n := n)) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : Matrix n n ℂ => M i j) h)

theorem complexify_matrix_spectrum (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    spectrum ℝ (A.map Complex.ofReal) = spectrum ℝ A := by
  have hs : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  exact hs.map_spectrum_real (ofRealMatrixStarAlgHom (n := n))
    ofRealMatrixStarAlgHom_injective
    (ofRealMatrixStarAlgHom (n := n)).toAlgHom.toLinearMap.continuous_of_finiteDimensional

end ComplexMatrices

section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.CombinedPolynomial RoughRegime.MatrixDeterminant
variable (r : ℕ) [NeZero r]

def complexParentValuation (A C : Matrix (Fin r) (Fin r) ℂ) : parentInverseVariables r → ℂ
  | Sum.inl ij => A ij.1 ij.2
  | Sum.inr ⟨_, ij⟩ => C ij.1 ij.2

theorem eval_renamed_series_complex {V W : Type*} (f : V → W) (values : W → ℂ)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
      PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (values ∘ f)) P := by
  ext k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  exact MvPolynomial.eval₂_rename _ _ _ _

theorem inverseVariableSeries_eval_complex (lo hi : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
      (inverseVariableSeries r (fun _ : Fin 1 => r) lo hi i j) = complexKernelSeries lo hi A i j := by
  rw [inverseVariableSeries, eval_renamed_series_complex]
  exact congrArg (fun K => K i j) (variableKernelSeries_eval_complex lo hi A)

theorem determinantVariableSeries_eval_complex (lo hi : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℂ) (t : Fin 1) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
      (determinantVariableSeries r (fun _ : Fin 1 => r) lo hi t) =
      (complexKernelSeries lo hi C).det := by
  rw [determinantVariableSeries, eval_renamed_series_complex]
  change PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun ij : Fin r × Fin r => C ij.1 ij.2))
    (variableKernelSeries lo hi).det = _
  rw [RingHom.map_det, variableKernelSeries_eval_complex]

theorem parentInverseEntryPolynomial_eval_complex (lo hi : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (m : ℕ) :
    MvPolynomial.eval₂ Complex.ofRealHom (complexParentValuation r A C)
      (parentInverseEntryPolynomial lo hi r m i j) =
      ((intervalGeometricMean lo hi ^ (r + 1))⁻¹ : ℝ) *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (complexKernelSeries lo hi A i j * (complexKernelSeries lo hi C).det) := by
  have he : PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
      (combinedVariableSeries r (fun _ : Fin 1 => r) lo hi i j) =
      complexKernelSeries lo hi A i j * (complexKernelSeries lo hi C).det := by
    simp only [combinedVariableSeries, map_mul, map_prod, inverseVariableSeries_eval_complex,
      determinantVariableSeries_eval_complex, Fin.prod_univ_one]
  simp only [parentInverseEntryPolynomial, truncationEntryPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum, combinedCoefficientPolynomial]
  simp only [Fin.sum_univ_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hc := congrArg (fun P => PowerSeries.coeff k P) he
  rw [PowerSeries.coeff_map] at hc
  exact hc

end ComplexFreeCoordinates

section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A concrete finite coefficient envelope for a real polynomial on a complex coordinate ball. -/
def polynomialCoordinateBound (P : MvPolynomial V ℝ) (R : ℝ) : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖ * ∏ j : V, R ^ α j

theorem polynomialCoordinateBound_nonneg (P : MvPolynomial V ℝ) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ polynomialCoordinateBound P R := by
  unfold polynomialCoordinateBound
  positivity

theorem polynomial_complex_coordinate_bound (P : MvPolynomial V ℝ) (z : V → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hz : ∀ j, ‖z j‖ ≤ R) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ polynomialCoordinateBound P R := by
  rw [MvPolynomial.eval₂_eq']
  calc
    _ ≤ ∑ α ∈ P.support, ‖Complex.ofRealHom (P.coeff α) * ∏ j : V, z j ^ α j‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_mul, norm_prod]
      change ‖(P.coeff α : ℂ)‖ * ∏ j : V, ‖z j ^ α j‖ ≤ _
      rw [Complex.norm_real]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun j hj => norm_nonneg _)
      intro j hj
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hz j) _

end PolynomialBounds

section CoordinateOperators
open scoped Matrix.Norms.L2Operator
variable (r : ℕ) [NeZero r]

def currentCoordinateMatrix : (incrementVariables r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z i j := z (Sum.inl (Sum.inl (i, j)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def parentCoordinateMatrix : (incrementVariables r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z i j := z (Sum.inl (Sum.inr ⟨0, (i, j)⟩))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def currentCoordinateCLM : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  (currentCoordinateMatrix r).toContinuousLinearMap

def parentCoordinateCLM : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  (parentCoordinateMatrix r).toContinuousLinearMap

@[simp] theorem currentCoordinateCLM_apply (z : incrementVariables r → ℂ) (i j : Fin r) :
    currentCoordinateCLM r z i j = z (Sum.inl (Sum.inl (i, j))) := rfl

@[simp] theorem parentCoordinateCLM_apply (z : incrementVariables r → ℂ) (i j : Fin r) :
    parentCoordinateCLM r z i j = z (Sum.inl (Sum.inr ⟨0, (i, j)⟩)) := rfl

theorem coordinate_parent_valuation (z : incrementVariables r → ℂ) :
    z ∘ Sum.inl = complexParentValuation r (currentCoordinateCLM r z) (parentCoordinateCLM r z) := by
  funext v
  cases v with
  | inl ij => rfl
  | inr t =>
    rcases t with ⟨t, ij⟩
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl

open RoughRegime.Upper

/-- The neighborhood radius is computed from fixed coordinate extraction operators. -/
def inverseCoordinateRadius (lo hi η : ℝ) : ℝ :=
  min 1 ((4 * perturbationConstant η)⁻¹ /
    max 1 (|(intervalHalfWidth lo hi)⁻¹| *
      (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖)))

theorem inverseCoordinateRadius_pos (lo hi η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    0 < inverseCoordinateRadius r lo hi η := by
  have hK := perturbationConstant_pos η hη hη1
  unfold inverseCoordinateRadius
  apply lt_min (by norm_num)
  apply div_pos (by positivity)
  exact (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)

theorem coordinate_normalized_perturbation (lo hi η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (z z₀ : incrementVariables r → ℂ)
    (hz : ‖z - z₀‖ < inverseCoordinateRadius r lo hi η)
    (F : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (hF : ‖F‖ ≤ ‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖) :
    ‖normalizeMatrix lo hi (F z) - normalizeMatrix lo hi (F z₀)‖ ≤
      (4 * perturbationConstant η)⁻¹ := by
  let D := max 1 (|(intervalHalfWidth lo hi)⁻¹| *
    (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖))
  have hD : 0 < D := (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have hz' : ‖z - z₀‖ ≤ (4 * perturbationConstant η)⁻¹ / D :=
    hz.le.trans (min_le_right _ _)
  rw [normalizeMatrix_sub, norm_smul, Real.norm_eq_abs, ← map_sub]
  calc
    _ ≤ |(intervalHalfWidth lo hi)⁻¹| * (‖F‖ * ‖z - z₀‖) :=
      mul_le_mul_of_nonneg_left (F.le_opNorm _) (abs_nonneg _)
    _ ≤ D * ‖z - z₀‖ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_left hF (abs_nonneg _)).trans (le_max_right _ _)
    _ ≤ _ := by simpa only [mul_comm] using (le_div_iff₀ hD).mp hz'

end CoordinateOperators

section UniformNeighborhood
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper
variable (r : ℕ) [NeZero r]

def inverseComplexEnvelope (lo hi q : ℝ) : ℝ :=
  |(intervalGeometricMean lo hi ^ (r + 1))⁻¹| *
    ((Fintype.card (Equiv.Perm (Fin r)) : ℝ) * 4 ^ (r + 1)) *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ k

def incrementComplexEnvelope (lo hi q L : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) : ℝ :=
  inverseComplexEnvelope r lo hi q *
    ∑ j : Fin r, polynomialCoordinateBound (numeratorPolynomial r T y j) (L + 1)

theorem inverseComplexEnvelope_nonneg (lo hi q : ℝ) (hq : 0 ≤ q) :
    0 ≤ inverseComplexEnvelope r lo hi q := by
  unfold inverseComplexEnvelope
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (fun k => by positivity)

theorem actual_increment_complex_neighborhood (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (L : ℝ) (hL : 0 ≤ L) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ)
    (z₀ z : incrementVariables r → ℂ) (hz₀ : ‖z₀‖ ≤ L)
    (hA : (currentCoordinateCLM r z₀).IsHermitian)
    (hC : (parentCoordinateCLM r z₀).IsHermitian)
    (hASpec : spectrum ℝ (currentCoordinateCLM r z₀) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (parentCoordinateCLM r z₀) ⊆ Set.Icc lo hi)
    (hz : ‖z - z₀‖ < inverseCoordinateRadius r lo hi η) (m : ℕ) (i : Fin r) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z (incrementEntryPolynomial r lo hi T y m i)‖ ≤
      incrementComplexEnvelope r lo hi (intervalRho lo hi / η) L T y := by
  have hρ := intervalRho_pos lo hi hlo hlt
  have hη : 0 < η := hρ.trans hρη
  have hq : 0 < intervalRho lo hi / η := div_pos hρ hη
  have hq1 : intervalRho lo hi / η < 1 := (div_lt_one hη).mpr hρη
  have hδ : 0 ≤ (4 * perturbationConstant η)⁻¹ :=
    (inv_pos.mpr (mul_pos (by norm_num) (perturbationConstant_pos η hη hη1))).le
  have hsmall : 4 * (4 * perturbationConstant η)⁻¹ * perturbationConstant η ≤ 1 := by
    have hK := ne_of_gt (perturbationConstant_pos η hη hη1)
    field_simp
    norm_num
  have hdA := coordinate_normalized_perturbation r lo hi η hη hη1 z z₀ hz
    (currentCoordinateCLM r) (le_add_of_nonneg_right (norm_nonneg _))
  have hdC := coordinate_normalized_perturbation r lo hi η hη hη1 z z₀ hz
    (parentCoordinateCLM r) (le_add_of_nonneg_left (norm_nonneg _))
  have hK := complex_kernel_entry_coefficient_bound lo hi hlo hlt
    (currentCoordinateCLM r z₀) (currentCoordinateCLM r z) hA hASpec η _ hη hη1 hδ hsmall hdA
  have hD := complex_kernel_entry_coefficient_bound lo hi hlo hlt
    (parentCoordinateCLM r z₀) (parentCoordinateCLM r z) hC hCSpec η _ hη hη1 hδ hsmall hdC
  have hzR : ∀ j, ‖z j‖ ≤ L + 1 := by
    intro j
    apply (norm_le_pi_norm z j).trans
    calc
      ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + L := add_le_add (hz.le.trans (min_le_left _ _)) hz₀
      _ = _ := by ring
  have hI (j : Fin r) :
      ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j))‖ ≤
        inverseComplexEnvelope r lo hi (intervalRho lo hi / η) := by
    rw [MvPolynomial.eval₂_rename, coordinate_parent_valuation,
      parentInverseEntryPolynomial_eval_complex, norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left
      (combined_truncation_uniform_bound _ _ _ 4 hq hq1 (by norm_num) hK hD i j m)
      (abs_nonneg _)).trans_eq (by simp [inverseComplexEnvelope, mul_assoc])
  simp only [incrementEntryPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul]
  calc
    _ ≤ ∑ j : Fin r, ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j)) *
        MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin r, inverseComplexEnvelope r lo hi (intervalRho lo hi / η) *
        polynomialCoordinateBound (numeratorPolynomial r T y j) (L + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hI j)
        (polynomial_complex_coordinate_bound _ z (L + 1) (by positivity) hzR)
        (norm_nonneg _) (inverseComplexEnvelope_nonneg r lo hi _ hq.le)
    _ = _ := by rw [← Finset.mul_sum]; rfl

end UniformNeighborhood

section ActualDerivatives
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.ComplexDerivativeBridge
variable (r : ℕ) [NeZero r]

/-- The paper's free moment polynomial after the canonical finite coordinate enumeration. -/
def incrementFinPolynomial (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
    (incrementEntryPolynomial r lo hi T y m i)

def currentRealCoordinateMatrix (u : incrementVariables r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inl (i, j)))

def parentRealCoordinateMatrix (u : incrementVariables r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inr ⟨0, (i, j)⟩))

private theorem norm_reindex_le {V W : Type*} [Fintype V] [Fintype W]
    (z : V → ℂ) (f : W → V) : ‖z ∘ f‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro j
  exact norm_le_pi_norm z (f j)

theorem actual_increment_derivative_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (L : ℝ) (hL : 0 ≤ L) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ)
    (u : incrementVariables r → ℝ) (hu : ‖u‖ ≤ L)
    (hA : (currentRealCoordinateMatrix r u).IsHermitian)
    (hC : (parentRealCoordinateMatrix r u).IsHermitian)
    (hASpec : spectrum ℝ (currentRealCoordinateMatrix r u) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (parentRealCoordinateMatrix r u) ⊆ Set.Icc lo hi)
    (m k : ℕ) (hk : 0 < k) (i : Fin r)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => u ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      incrementComplexEnvelope r lo hi (intervalRho lo hi / η) L T y * (k.factorial : ℝ) *
        (Real.exp 1 / inverseCoordinateRadius r lo hi η) ^ k * ∏ j, ‖v j‖ := by
  have hη : 0 < η := (intervalRho_pos lo hi hlo hlt).trans hρη
  let uFin := fun j => u ((Fintype.equivFin (incrementVariables r)).symm j)
  let z₀ : incrementVariables r → ℂ := fun j => (u j : ℂ)
  have hz₀ : ‖z₀‖ ≤ L := by
    apply (pi_norm_le_iff_of_nonneg hL).mpr
    intro j
    have hj : ‖z₀ j‖ ≤ ‖u‖ := by simpa [z₀] using norm_le_pi_norm u j
    exact hj.trans hu
  have hmapA : currentCoordinateCLM r z₀ = (currentRealCoordinateMatrix r u).map Complex.ofReal := rfl
  have hmapC : parentCoordinateCLM r z₀ = (parentRealCoordinateMatrix r u).map Complex.ofReal := rfl
  have hA' : (currentCoordinateCLM r z₀).IsHermitian := by
    rw [hmapA]
    exact hA.map _ (fun x => by simp)
  have hC' : (parentCoordinateCLM r z₀).IsHermitian := by
    rw [hmapC]
    exact hC.map _ (fun x => by simp)
  have hASpec' : spectrum ℝ (currentCoordinateCLM r z₀) ⊆ Set.Icc lo hi := by
    rw [hmapA, complexify_matrix_spectrum _ hA]
    exact hASpec
  have hCSpec' : spectrum ℝ (parentCoordinateCLM r z₀) ⊆ Set.Icc lo hi := by
    rw [hmapC, complexify_matrix_spectrum _ hC]
    exact hCSpec
  apply real_polynomial_derivative_bound _ uFin _ _
    (inverseCoordinateRadius_pos r lo hi η hη hη1) _ hk v
  intro z hz
  rw [complexify, MvPolynomial.eval_map, incrementFinPolynomial, MvPolynomial.eval₂_rename]
  apply actual_increment_complex_neighborhood r lo hi hlo hlt η hρη hη1 L hL T y
    z₀ (z ∘ Fintype.equivFin (incrementVariables r)) hz₀ hA' hC' hASpec' hCSpec' _ m i
  have he : z ∘ Fintype.equivFin (incrementVariables r) - z₀ =
      (z - (fun j => (uFin j : ℂ))) ∘ Fintype.equivFin (incrementVariables r) := by
    funext j
    simp [z₀, uFin]
  rw [he]
  exact (norm_reindex_le _ _).trans_lt hz

end ActualDerivatives
end NearlyMinimax
