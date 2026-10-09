module

public import NearlyMinimax.GaussianPrimitiveSeparated


@[expose] public section

/-! Actual polynomial products in the Gaussian separated marks are single
monomials. Their frame coefficient cost is exponential only in the number
of factors, uniformly in the ambient frame order. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def gaussianAffineExponent {d : ℕ} (a : Fin d) (s : Bool) : Fin d →₀ ℕ :=
  if s then Finsupp.single a 1 else 0

def gaussianAffineCoefficient (s : Bool) : ℝ := if s then -8 else 2

theorem gaussianAffinePolynomial_monomial {d : ℕ} (a : Fin d) (s : Bool) :
    gaussianAffinePolynomial a s =
      monomial (gaussianAffineExponent a s) (gaussianAffineCoefficient s) := by
  cases s <;> simp only [gaussianAffinePolynomial, gaussianAffineExponent, gaussianAffineCoefficient,
    Bool.false_eq_true, ite_false, ite_true, C_apply, X, monomial_mul_monomial,
    zero_add, mul_one]

def gaussianPolynomialProduct {κ : Type*} [Fintype κ] {d : ℕ}
    (a : κ → Fin d) (s : κ → Bool) : MvPolynomial (Fin d) ℝ := ∏ i, gaussianAffinePolynomial (a i) (s i)

theorem gaussianPolynomialProduct_monomial {κ : Type*} [Fintype κ] {d : ℕ}
    (a : κ → Fin d) (s : κ → Bool) :
    gaussianPolynomialProduct a s =
      monomial (∑ i, gaussianAffineExponent (a i) (s i)) (∏ i, gaussianAffineCoefficient (s i)) := by
  unfold gaussianPolynomialProduct
  simp_rw [gaussianAffinePolynomial_monomial]
  exact (monomial_sum_prod _ _ _).symm

theorem gaussianAffineCoefficient_abs_le_eight (s : Bool) : |gaussianAffineCoefficient s| ≤ 8 := by
  cases s <;> norm_num [gaussianAffineCoefficient]

theorem gaussianPolynomialProduct_coefficient_bound {κ : Type*} [Fintype κ]
    (s : κ → Bool) :
    |∏ i, gaussianAffineCoefficient (s i)| ≤ (8 : ℝ) ^ Fintype.card κ := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : κ, (8 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun i _ => gaussianAffineCoefficient_abs_le_eight (s i))
    _ = _ := by simp

theorem gaussianPolynomialProduct_frame_cost {κ : Type*} [Fintype κ] {d D : ℕ}
    (a : κ → Fin d) (s : κ → Bool) :
    (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct a s) β|) ≤
      (8 : ℝ) ^ Fintype.card κ := by
  classical
  have hinj : Function.Injective (fun β : HighFrameIndex d D => polynomialBoxExponent β.val) := by
    intro β β' h
    exact Subtype.ext (polynomial_box_exponent_injective h)
  rw [gaussianPolynomialProduct_monomial]
  have he (β : HighFrameIndex d D) :
      |highFrameCoefficients (monomial (∑ i, gaussianAffineExponent (a i) (s i))
        (∏ i, gaussianAffineCoefficient (s i))) β| =
      |∏ i, gaussianAffineCoefficient (s i)| *
        (if (∑ i, gaussianAffineExponent (a i) (s i)) = polynomialBoxExponent β.val then 1 else 0) := by
    simp only [highFrameCoefficients, coeff_monomial]
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  have h := finite_injective_indicator_sum_le_one _ hinj (∑ i, gaussianAffineExponent (a i) (s i))
  calc
    _ ≤ |∏ i, gaussianAffineCoefficient (s i)| * 1 := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using gaussianPolynomialProduct_coefficient_bound s

theorem gaussianAffinePolynomial_degree {d : ℕ} (a : Fin d) (s : Bool) :
    (gaussianAffinePolynomial a s).totalDegree ≤ 1 := by
  cases s
  · simp [gaussianAffinePolynomial]
  · simp only [gaussianAffinePolynomial, ite_true]
    exact (totalDegree_mul _ _).trans (by simp)

theorem gaussianPolynomialProduct_degree {κ : Type*} [Fintype κ] {d : ℕ}
    (a : κ → Fin d) (s : κ → Bool) :
    (gaussianPolynomialProduct a s).totalDegree ≤ Fintype.card κ := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : κ, 1 := Finset.sum_le_sum (fun i _ => gaussianAffinePolynomial_degree (a i) (s i))
    _ = _ := by simp

/-- Uniform finite-frame coefficient cost of the actual rank-one product
amplitude, derived from its monomial products. -/
theorem gaussianPolynomialProduct_rankone_cost {κ κ' : Type*} [Fintype κ] [Fintype κ']
    {d D : ℕ} (a : κ → Fin d) (s : κ → Bool) (b : κ' → Fin d) (s' : κ' → Bool) (c : ℝ) :
    (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
      |c * highFrameCoefficients (gaussianPolynomialProduct a s) β *
        highFrameCoefficients (gaussianPolynomialProduct b s') β'|) ≤
      |c| * (8 : ℝ) ^ (Fintype.card κ + Fintype.card κ') := by
  have he : (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
      |c * highFrameCoefficients (gaussianPolynomialProduct a s) β *
        highFrameCoefficients (gaussianPolynomialProduct b s') β'|) =
      |c| * (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct a s) β|) *
      (∑ β' : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct b s') β'|) := by
    simp only [abs_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he, pow_add, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  exact mul_le_mul (gaussianPolynomialProduct_frame_cost a s)
    (gaussianPolynomialProduct_frame_cost b s')
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)

end NearlyMinimax
