module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic


@[expose] public section

/-!
# Finite moment rules

The finite signed rules below are represented by their finite weighted-sum action.
This retains coincident atoms (so the sum of absolute weights is an upper bound on
measure total variation). Polynomial degree bounds count the number of distinct
nodes, and no interpolation property is assumed as a hypothesis.
-/

noncomputable section

namespace NearlyMinimax

open Polynomial Finset

section Cardinal

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- Applying cardinal evaluation weights is evaluation at the chosen point. -/
theorem cardinal_evaluation_exact (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (P : F[X]) (hP : P.degree < s.card) (x : F) :
    (∑ i ∈ s, (Lagrange.basis s v i).eval x * P.eval (v i)) = P.eval x := by
  have h := congrArg (fun p : F[X] => p.eval x) (Lagrange.eq_interpolate hv hP)
  simpa only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C,
    mul_comm] using h.symm

/-- Coefficients of cardinal polynomials extract that coefficient exactly. -/
theorem cardinal_coefficient_exact (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (P : F[X]) (hP : P.degree < s.card) (a : ℕ) :
    (∑ i ∈ s, (Lagrange.basis s v i).coeff a * P.eval (v i)) = P.coeff a := by
  have h := congrArg (fun p : F[X] => p.coeff a) (Lagrange.eq_interpolate hv hP)
  simp only [Lagrange.interpolate_apply, finset_sum_coeff, coeff_C_mul] at h
  simpa only [mul_comm] using h.symm

/-- Differentiating cardinal interpolation gives the finite derivative rule. -/
theorem cardinal_derivative_exact (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (P : F[X]) (hP : P.degree < s.card) (x : F) :
    (∑ i ∈ s, (Lagrange.basis s v i).derivative.eval x * P.eval (v i)) =
      P.derivative.eval x := by
  have h := congrArg (fun p : F[X] => p.derivative.eval x)
    (Lagrange.eq_interpolate hv hP)
  simp only [Lagrange.interpolate_apply, derivative_sum, derivative_C_mul,
    eval_finset_sum, eval_mul, eval_C] at h
  simpa only [mul_comm] using h.symm

/-- The exterior cardinal weight has the product formula in Lemma 3(a). -/
theorem cardinal_weight_at_zero (s : Finset ι) (v : ι → F) (i : ι) :
    (Lagrange.basis s v i).eval 0 = ∏ j ∈ s.erase i, v j / (v j - v i) := by
  simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul,
    eval_C, eval_sub, eval_X, zero_sub]
  apply Finset.prod_congr rfl
  intro j hj
  rw [show v i - v j = -(v j - v i) by ring, inv_neg]
  simp [div_eq_mul_inv, mul_comm]

/-- The explicit exterior product rule reproduces every polynomial in its degree range. -/
theorem exterior_product_rule_exact (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (P : F[X]) (hP : P.degree < s.card) :
    (∑ i ∈ s, (∏ j ∈ s.erase i, v j / (v j - v i)) * P.eval (v i)) = P.eval 0 := by
  simpa only [cardinal_weight_at_zero] using cardinal_evaluation_exact s v hv P hP 0

/-- The coefficient rule has Kronecker monomial moments. -/
theorem cardinal_coefficient_monomial (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a b : ℕ) (hb : b < s.card) :
    (∑ i ∈ s, (Lagrange.basis s v i).coeff a * (v i) ^ b) =
      if b = a then 1 else 0 := by
  have hd : (X ^ b : F[X]).degree < s.card := by
    simpa only [degree_X_pow, Nat.cast_withBot] using (WithBot.coe_lt_coe.mpr hb)
  simpa [coeff_X_pow, eq_comm] using cardinal_coefficient_exact s v hv (X ^ b) hd a

end Cardinal

/-- The fixed scalar-response nodes from Lemma 3(c). -/
def responseNode (q : ℕ) (j : Fin (2 * q + 2)) : ℝ :=
  (j.val : ℝ) / (2 * q + 1 : ℕ)

theorem responseNode_injective (q : ℕ) : Function.Injective (responseNode q) := by
  intro i j hij
  have hn : (2 * q + 1 : ℝ) ≠ 0 := by positivity
  have h : (i.val : ℝ) = j.val := by
    apply (div_left_inj' hn).mp
    simpa [responseNode] using hij
  exact Fin.ext (by exact_mod_cast h)

/-- The scalar-response extraction weights. -/
def responseWeight (q : ℕ) (j : Fin (2 * q + 2)) : ℝ :=
  (Lagrange.basis Finset.univ (responseNode q) j).coeff 2

/-- The paper's fixed rule extracts the quadratic coefficient, including zero mass and mean. -/
theorem response_rule_moments (q a : ℕ) (ha : a ≤ 2 * q + 1) :
    (∑ j : Fin (2 * q + 2), responseWeight q j * (responseNode q j) ^ a) =
      if a = 2 then 1 else 0 := by
  exact cardinal_coefficient_monomial Finset.univ (responseNode q)
    (responseNode_injective q).injOn 2 a (by simpa using (show a < 2 * q + 2 by omega))

/-- Exactness of the fixed quadratic-extraction rule on every polynomial of the stated degree. -/
theorem response_rule_exact (q : ℕ) (P : ℝ[X]) (hP : P.degree < 2 * q + 2) :
    (∑ j : Fin (2 * q + 2), responseWeight q j * P.eval (responseNode q j)) =
      P.coeff 2 := by
  exact cardinal_coefficient_exact Finset.univ (responseNode q)
    (responseNode_injective q).injOn P (by simpa using hP) 2

/-- The fixed response rule has zero total mass. -/
theorem response_zero_mass (q : ℕ) :
    (∑ j : Fin (2 * q + 2), responseWeight q j) = 0 := by
  simpa using response_rule_moments q 0 (by omega)

/-- The fixed response rule has zero first moment. -/
theorem response_zero_mean (q : ℕ) :
    (∑ j : Fin (2 * q + 2), responseWeight q j * responseNode q j) = 0 := by
  simpa using response_rule_moments q 1 (by omega)

/-- When at least three nodes are present, the second moment is one. -/
theorem response_second_moment (q : ℕ) (hq : 1 ≤ q) :
    (∑ j : Fin (2 * q + 2), responseWeight q j * responseNode q j ^ 2) = 1 := by
  simpa using response_rule_moments q 2 (by omega)

/-- Quadratic extraction after an affine reset is the squared reset displacement. -/
theorem response_quadratic_reset (q : ℕ) (hq : 1 ≤ q) (a b d c v : ℝ) :
    (∑ j : Fin (2 * q + 2), responseWeight q j *
      (a + b * (c + responseNode q j * (v - c)) +
        d * (c + responseNode q j * (v - c)) ^ 2)) = d * (v - c) ^ 2 := by
  calc
    _ = ∑ j : Fin (2 * q + 2),
      ((a + b * c + d * c ^ 2) * responseWeight q j +
      (b * (v - c) + 2 * d * c * (v - c)) *
        (responseWeight q j * responseNode q j) +
      (d * (v - c) ^ 2) * (responseWeight q j * responseNode q j ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        response_zero_mass, response_zero_mean, response_second_moment q hq,
        mul_zero, mul_one, zero_add]

/-- A fair sign, represented on the two-point Boolean space. -/
def fairSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem fairSign_abs (b : Bool) : |fairSign b| = 1 := by cases b <;> norm_num [fairSign]

private theorem finite_sum_abs_bound {κ : Type*} [Fintype κ] (g b : κ → ℝ)
    (h : ∀ k, |g k| ≤ b k) : |∑ k, g k| ≤ ∑ k, b k := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun k hk => h k))

section Covariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fixed atoms of the covariance rule. They do not depend on the matrix. -/
def covarianceAtom (C : ℝ) (i j : ι) (s t : Bool) : ι → ℝ :=
  fun k => (fairSign s * (if i = k then 1 else 0) +
    fairSign t * (if j = k then 1 else 0)) / (2 * C)

/-- The factor `1/4` from fair sign averaging is included in the weight. -/
def covarianceWeight (C : ℝ) (A : ι → ι → ℝ) (i j : ι) (s t : Bool) : ℝ :=
  C ^ 2 / 2 * A i j * fairSign s * fairSign t

/-- The finite signed covariance kernel evaluated against a function. -/
def covarianceAction (C : ℝ) (A : ι → ι → ℝ) (f : (ι → ℝ) → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ s : Bool, ∑ t : Bool,
    covarianceWeight C A i j s t * f (covarianceAtom C i j s t)

private theorem sign_mass (C a : ℝ) :
    (∑ s : Bool, ∑ t : Bool, C ^ 2 / 2 * a * fairSign s * fairSign t) = 0 := by
  simp [fairSign]

private theorem sign_mean (C a x y : ℝ) :
    (∑ s : Bool, ∑ t : Bool,
      (C ^ 2 / 2 * a * fairSign s * fairSign t) *
        ((fairSign s * x + fairSign t * y) / (2 * C))) = 0 := by
  simp [fairSign]
  ring

private theorem sign_second (C a x y u v : ℝ) (hC : C ≠ 0) :
    (∑ s : Bool, ∑ t : Bool,
      (C ^ 2 / 2 * a * fairSign s * fairSign t) *
        (((fairSign s * x + fairSign t * y) / (2 * C)) *
          ((fairSign s * u + fairSign t * v) / (2 * C)))) =
      a / 2 * (x * v + y * u) := by
  simp only [Fintype.sum_bool, fairSign, Bool.false_eq_true, ↓reduceIte]
  field_simp
  ring

/-- The action is additive in the test function. -/
theorem covarianceAction_add (C : ℝ) (A : ι → ι → ℝ)
    (f g : (ι → ℝ) → ℝ) :
    covarianceAction C A (fun x => f x + g x) =
      covarianceAction C A f + covarianceAction C A g := by
  simp only [covarianceAction, mul_add, Finset.sum_add_distrib]

/-- The action is homogeneous in the test function. -/
theorem covarianceAction_mul (C a : ℝ) (A : ι → ι → ℝ)
    (f : (ι → ℝ) → ℝ) :
    covarianceAction C A (fun x => a * f x) = a * covarianceAction C A f := by
  simp only [covarianceAction, mul_left_comm, Finset.mul_sum]

/-- The action commutes with a finite sum of test functions. -/
theorem covarianceAction_sum {κ : Type*} (S : Finset κ) (C : ℝ)
    (A : ι → ι → ℝ) (f : κ → (ι → ℝ) → ℝ) :
    covarianceAction C A (fun x => ∑ i ∈ S, f i x) =
      ∑ i ∈ S, covarianceAction C A (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [covarianceAction]
  | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      rw [covarianceAction_add, ih]

/-- The covariance rule annihilates constants. -/
theorem covariance_zero_mass (C : ℝ) (A : ι → ι → ℝ) :
    covarianceAction C A (fun _ => 1) = 0 := by
  simp only [covarianceAction, covarianceWeight, mul_one]
  simp_rw [sign_mass]
  simp

/-- The covariance rule annihilates each coordinate. -/
theorem covariance_zero_mean (C : ℝ) (A : ι → ι → ℝ) (k : ι) :
    covarianceAction C A (fun x => x k) = 0 := by
  simp only [covarianceAction, covarianceWeight, covarianceAtom]
  simp_rw [sign_mean]
  simp

/-- Without a symmetry assumption the second moment is the matrix's symmetric part. -/
theorem covariance_second_moment (C : ℝ) (A : ι → ι → ℝ) (hC : C ≠ 0) (k l : ι) :
    covarianceAction C A (fun x => x k * x l) = (A k l + A l k) / 2 := by
  simp only [covarianceAction, covarianceWeight, covarianceAtom]
  simp_rw [sign_second C _ _ _ _ _ hC]
  simp [mul_add, Finset.sum_add_distrib, mul_ite]
  ring

/-- For symmetric matrices the covariance rule has precisely the prescribed second moment. -/
theorem covariance_second_moment_symmetric (C : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (k l : ι) :
    covarianceAction C A (fun x => x k * x l) = A k l := by
  rw [covariance_second_moment C A hC, hA l k]
  ring

/-- Every affine function is annihilated by the signed covariance rule. -/
theorem covariance_affine_annihilation (C a : ℝ) (A : ι → ι → ℝ) (b : ι → ℝ) :
    covarianceAction C A (fun x => a + ∑ k, b k * x k) = 0 := by
  rw [covarianceAction_add]
  have hc : covarianceAction C A (fun _ => a) = 0 := by
    simpa using (covarianceAction_mul C a A (fun _ => 1)).trans
      (by rw [covariance_zero_mass, mul_zero])
  rw [hc, covarianceAction_sum]
  simp_rw [covarianceAction_mul, covariance_zero_mean, mul_zero]
  simp

/-- Quadratic matrix forms integrate to their contraction against the prescribed covariance. -/
theorem covariance_quadratic_form (C : ℝ) (A Q : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) :
    covarianceAction C A (fun x => ∑ k, ∑ l, Q k l * (x k * x l)) =
      ∑ k, ∑ l, Q k l * A k l := by
  rw [covarianceAction_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [covarianceAction_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [covarianceAction_mul, covariance_second_moment_symmetric C A hC hA]

/-- Each atom lies in the coefficient ball of radius `1/C`. -/
theorem covarianceAtom_mem_ball (C : ℝ) (hC : 0 < C) (i j : ι) (s t : Bool) :
    (∑ k, |covarianceAtom C i j s t k|) ≤ C⁻¹ := by
  have hden : 0 < 2 * C := by positivity
  calc
    (∑ k, |covarianceAtom C i j s t k|) ≤
        ∑ k, (|(fairSign s * (if i = k then 1 else 0))| +
          |(fairSign t * (if j = k then 1 else 0))|) / (2 * C) := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp [covarianceAtom]
      rw [abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (le_of_lt hden)
    _ = C⁻¹ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp [apply_ite abs]
      field_simp
      ring

/-- The sum of absolute atom weights is the variation bound in the paper. -/
theorem covariance_weight_variation (C : ℝ) (A : ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ s : Bool, ∑ t : Bool, |covarianceWeight C A i j s t|) =
      2 * C ^ 2 * ∑ i, ∑ j, |A i j| := by
  have hw (i j : ι) (s t : Bool) : |covarianceWeight C A i j s t| = C ^ 2 / 2 * |A i j| := by
    dsimp [covarianceWeight]
    rw [abs_mul, abs_mul, abs_mul, abs_div]
    simp [abs_of_nonneg (sq_nonneg C)]
  simp_rw [hw]
  simp only [Fintype.sum_bool]
  calc
    (∑ i, ∑ j, (C ^ 2 / 2 * |A i j| + C ^ 2 / 2 * |A i j| +
      (C ^ 2 / 2 * |A i j| + C ^ 2 / 2 * |A i j|))) =
      ∑ i, ∑ j, 2 * C ^ 2 * |A i j| := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by simp only [Finset.mul_sum]

/-- The signed-rule action is bounded by the atom variation times a uniform bound. -/
theorem covarianceAction_abs_le (C B : ℝ) (A : ι → ι → ℝ)
    (f : (ι → ℝ) → ℝ)
    (hf : ∀ i j s t, |f (covarianceAtom C i j s t)| ≤ B) :
    |covarianceAction C A f| ≤ (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) * B := by
  have ht (i j : ι) (s t : Bool) :
      |covarianceWeight C A i j s t * f (covarianceAtom C i j s t)| ≤
        |covarianceWeight C A i j s t| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf i j s t) (abs_nonneg _)
  have h := finite_sum_abs_bound
    (fun (i : ι) => ∑ (j : ι), ∑ s : Bool, ∑ t : Bool,
      covarianceWeight C A i j s t * f (covarianceAtom C i j s t))
    (fun (i : ι) => ∑ (j : ι), ∑ s : Bool, ∑ t : Bool, |covarianceWeight C A i j s t| * B)
    (fun (i : ι) => finite_sum_abs_bound _ _ (fun (j : ι) =>
      finite_sum_abs_bound _ _ (fun (s : Bool) => finite_sum_abs_bound _ _ (ht i j s))))
  simpa only [covarianceAction, ← Finset.sum_mul, covariance_weight_variation] using h

/-- Kernel weights depend linearly on the prescribed matrix. -/
theorem covarianceWeight_add (C : ℝ) (A B : ι → ι → ℝ) (i j : ι) (s t : Bool) :
    covarianceWeight C (fun i j => A i j + B i j) i j s t =
      covarianceWeight C A i j s t + covarianceWeight C B i j s t := by
  dsimp [covarianceWeight]
  ring

end Covariance

end NearlyMinimax
