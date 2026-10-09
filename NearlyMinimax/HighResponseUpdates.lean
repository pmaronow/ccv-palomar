module

public import NearlyMinimax.AtomicVariation
public import NearlyMinimax.LowSmoothnessVariance


@[expose] public section

/-! Actual finite scalar extraction and signed covariance resets of the
high-smoothness local response operator. -/
noncomputable section
open MeasureTheory Set Polynomial
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A ternary response on an affine regression line, as an actual polynomial. -/
def ternaryLinePolynomial (a f V δ : ℝ) (y : Fin 3) : ℝ[X] :=
  C (ternaryMass a f V y) + monomial 1 (δ * ternaryMeanDerivative a f y) +
    monomial 2 (δ ^ 2 * ternaryVarianceDerivative a y)

theorem ternary_line_polynomial_eval (a f V δ z : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).eval z = ternaryMass a (f + z * δ) V y := by
  fin_cases y <;> simp [ternaryLinePolynomial, ternaryMass, ternaryMeanDerivative,
    ternaryVarianceDerivative, div_eq_mul_inv] <;> ring

theorem ternary_line_polynomial_natDegree (a f V δ : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).natDegree ≤ 2 := by
  unfold ternaryLinePolynomial
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le (by simp) ((natDegree_monomial_le _).trans (by norm_num))
  · exact natDegree_monomial_le _

/-- Complete finite product likelihood on the same line. -/
def responseLinePolynomial (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) : ℝ[X] := ∏ i, ternaryLinePolynomial a (f i) V (δ i) (y i)

theorem response_line_polynomial_eval (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) :
    (responseLinePolynomial n a V f δ y).eval z =
      ∏ i, ternaryMass a (f i + z * δ i) V (y i) := by
  simp only [responseLinePolynomial, eval_prod]
  simp only [ternary_line_polynomial_eval]

theorem response_line_polynomial_natDegree (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) : (responseLinePolynomial n a V f δ y).natDegree ≤ 2 * n := by
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum (fun i _ => ternary_line_polynomial_natDegree _ _ _ _ _)
    _ = _ := by simp [mul_comm]

/-- Exact cardinal quadratic extraction of the genuine likelihood through
count q, including arbitrary offsets and incoming regression fields. -/
theorem response_line_rule_exact (q n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) (hn : n ≤ q) :
    (∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)) =
      (responseLinePolynomial n a V f δ y).coeff 2 := by
  simpa only [response_line_polynomial_eval] using response_rule_exact q
    (responseLinePolynomial n a V f δ y)
    (degree_le_natDegree.trans_lt (by
      exact_mod_cast (show (responseLinePolynomial n a V f δ y).natDegree < 2 * q + 2 from
        (response_line_polynomial_natDegree n a V f δ y).trans_lt (by omega))))

/-- Formal quadratic coefficient equals half the genuine second directional
product derivative, so its heat contraction can be evaluated explicitly. -/
theorem response_line_quadratic_coefficient (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) :
    2 * (responseLinePolynomial n a V f δ y).coeff 2 =
      finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ i) V (y i))
        (fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i))
        (fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 := by
  let Q := responseLinePolynomial n a V f δ y
  let H : Fin n → ℝ → ℝ := fun i z => ternaryMass a (f i + z * δ i) V (y i)
  let D : Fin n → ℝ → ℝ := fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)
  have hH (i : Fin n) (z : ℝ) : HasDerivAt (H i) (D i z) z := by
    have h := (ternary_hasDerivAt_mean a (f i + z * δ i) V (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))
    exact h.congr_deriv (by dsimp [D]; ring)
  have hD (i : Fin n) (z : ℝ) : HasDerivAt (D i) (E i z) z := by
    have h := ((ternary_hasDerivAt_mean_derivative a (f i + z * δ i) (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))).const_mul (δ i)
    exact h.congr_deriv (by dsimp [E]; ring)
  have hQ (z : ℝ) : HasDerivAt (fun z => Q.eval z) (finiteProductFirst Finset.univ H D z) z := by
    simpa only [Q, response_line_polynomial_eval] using
      finite_product_hasDerivAt Finset.univ H D z (fun i _ => hH i z)
  have hd : (fun z => Q.derivative.eval z) = finiteProductFirst Finset.univ H D := by
    funext z
    exact (Q.hasDerivAt z).unique (hQ z)
  have hsecond := finite_product_first_hasDerivAt Finset.univ H D E 0
    (fun i _ => hH i 0) (fun i _ => hD i 0)
  rw [← hd] at hsecond
  have he := (Q.derivative.hasDerivAt 0).unique hsecond
  change Q.derivative.derivative.eval 0 = finiteProductSecond Finset.univ H D E 0 at he
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative] at he
  norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.zero_add] at he
  simpa only [mul_comm, Q, H, D, E] using he

/-- A uniform second-derivative estimate yields an affine Taylor remainder
bound at every scalar response mark; no score bound is assumed. -/
theorem affine_line_remainder_abs_bound (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Icc (0 : ℝ) 1, |E z| ≤ B)
    (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : |H z - H 0 - z * D 0| ≤ B := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hDdiff (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : |D u - D 0| ≤ B := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hD x hx).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hE x hx)
      (convex_Icc (0 : ℝ) 1) hzero hu
    simp only [Real.norm_eq_abs, sub_zero] at h
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    exact h.trans (mul_le_mul_of_nonneg_left huabs hB |>.trans_eq (mul_one B))
  let G := fun u => H u - H 0 - u * D 0
  have hG (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : HasDerivAt G (D u - D 0) u :=
    (((hH u hu).sub_const (H 0)).sub ((hasDerivAt_id u).mul_const (D 0))).congr_deriv (by ring)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hG x hx).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hDdiff x hx)
    (convex_Icc (0 : ℝ) 1) hzero hz
  have hzabs : |z| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  simp only [G, sub_zero, zero_mul, sub_self, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left hzabs hB |>.trans_eq (mul_one B))

/-- The real scalar cardinal action has the all-count quadratic derivative
bound; its affine part cancels exactly by the proved moments. -/
theorem response_scalar_action_abs_bound (q : ℕ) (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Icc (0 : ℝ) 1, |E z| ≤ B)
    (hnodes : ∀ j : Fin (2 * q + 2), responseNode q j ∈ Icc (0 : ℝ) 1) :
    |∑ j : Fin (2 * q + 2), responseWeight q j * H (responseNode q j)| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) * B := by
  have he : (∑ j : Fin (2 * q + 2), responseWeight q j * H (responseNode q j)) =
      ∑ j : Fin (2 * q + 2), responseWeight q j *
        (H (responseNode q j) - H 0 - responseNode q j * D 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, response_zero_mass, response_zero_mean]
    simp
  rw [he]
  calc
    _ ≤ ∑ j : Fin (2 * q + 2), |responseWeight q j *
      (H (responseNode q j) - H 0 - responseNode q j * D 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (2 * q + 2), |responseWeight q j| * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (affine_line_remainder_abs_bound H D E B hB
        hH hD hE _ (hnodes j)) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Incoming coefficients are reset by the actual scalar mark and covariance atom. -/
def coefficientReset (c v : ι → ℝ) (z : ℝ) : ι → ℝ :=
  fun i => (1 - z) * c i + z * v i

/-- The paper's B_A as a genuine finite signed action. -/
def responseMatrixAction (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  covarianceAction C A (fun v => ∑ j : Fin (2 * q + 2),
    responseWeight q j * Φ (coefficientReset c v (responseNode q j)))

theorem responseMatrixAction_zero_mass (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) :
    responseMatrixAction q C A c (fun _ => 1) = 0 := by
  simp [responseMatrixAction, response_zero_mass, covarianceAction]

theorem responseMatrixAction_zero_mean (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (i : ι) : responseMatrixAction q C A c (fun v => v i) = 0 := by
  have hr (v : ι → ℝ) :
      (∑ j : Fin (2 * q + 2), responseWeight q j * coefficientReset c v (responseNode q j) i) = 0 := by
    have he (j : Fin (2 * q + 2)) :
        responseWeight q j * coefficientReset c v (responseNode q j) i =
          c i * responseWeight q j + (v i - c i) * (responseWeight q j * responseNode q j) := by
      dsimp [coefficientReset]
      ring
    simp_rw [he]
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, response_zero_mass, response_zero_mean]
  simp only [responseMatrixAction, hr, covarianceAction, mul_zero, Finset.sum_const_zero]

theorem responseMatrixAction_add (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ Ψ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C A c (fun v => Φ v + Ψ v) =
      responseMatrixAction q C A c Φ + responseMatrixAction q C A c Ψ := by
  simp only [responseMatrixAction, mul_add, Finset.sum_add_distrib, covarianceAction_add]

theorem responseMatrixAction_mul (q : ℕ) (C b : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C A c (fun v => b * Φ v) = b * responseMatrixAction q C A c Φ := by
  simp only [responseMatrixAction, mul_left_comm, ← Finset.mul_sum, covarianceAction_mul]

theorem responseMatrixAction_sum {κ : Type*} (S : Finset κ) (q : ℕ) (C : ℝ)
    (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : κ → (ι → ℝ) → ℝ) :
    responseMatrixAction q C A c (fun v => ∑ i ∈ S, Φ i v) =
      ∑ i ∈ S, responseMatrixAction q C A c (Φ i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [responseMatrixAction, covarianceAction]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [responseMatrixAction_add, ih]

theorem covariance_displacement_second (C : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (c : ι → ℝ) (k l : ι) :
    covarianceAction C A (fun v => (v k - c k) * (v l - c l)) = A k l := by
  have hf : (fun v : ι → ℝ => (v k - c k) * (v l - c l)) =
      (fun v => v k * v l + (-c l) * v k + (-c k) * v l + c k * c l * 1) := by
    funext v
    ring
  rw [hf, covarianceAction_add, covarianceAction_add, covarianceAction_add,
    covarianceAction_mul, covarianceAction_mul, covarianceAction_mul,
    covariance_second_moment_symmetric C A hC hA, covariance_zero_mean,
    covariance_zero_mean, covariance_zero_mass]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem response_reset_bilinear (q : ℕ) (hq : 1 ≤ q) (c v : ι → ℝ) (k l : ι) :
    (∑ j : Fin (2 * q + 2), responseWeight q j *
      (coefficientReset c v (responseNode q j) k * coefficientReset c v (responseNode q j) l)) =
      (v k - c k) * (v l - c l) := by
  have he (j : Fin (2 * q + 2)) :
      responseWeight q j *
        (coefficientReset c v (responseNode q j) k * coefficientReset c v (responseNode q j) l) =
      (c k * c l) * responseWeight q j +
        (c k * (v l - c l) + (v k - c k) * c l) * (responseWeight q j * responseNode q j) +
        ((v k - c k) * (v l - c l)) * (responseWeight q j * (responseNode q j) ^ 2) := by
    dsimp [coefficientReset]
    ring
  simp_rw [he]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, response_zero_mass,
    response_zero_mean, response_second_moment q hq]

theorem responseMatrixAction_second_moment (q : ℕ) (hq : 1 ≤ q) (C : ℝ)
    (A : ι → ι → ℝ) (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (c : ι → ℝ) (k l : ι) :
    responseMatrixAction q C A c (fun v => v k * v l) = A k l := by
  simp only [responseMatrixAction, response_reset_bilinear q hq]
  exact covariance_displacement_second C A hC hA c k l

/-- The full response operator has exact quadratic contraction at every
incoming coefficient state, independently of the frame dimension. -/
theorem responseMatrixAction_quadratic_form (q : ℕ) (hq : 1 ≤ q) (C : ℝ)
    (A Q : ι → ι → ℝ) (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (c : ι → ℝ) :
    responseMatrixAction q C A c (fun v => ∑ k, ∑ l, Q k l * (v k * v l)) =
      ∑ k, ∑ l, Q k l * A k l := by
  rw [responseMatrixAction_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [responseMatrixAction_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [responseMatrixAction_mul, responseMatrixAction_second_moment q hq C A hC hA]

theorem responseNode_mem_unit (q : ℕ) (j : Fin (2 * q + 2)) :
    responseNode q j ∈ Icc (0 : ℝ) 1 := by
  have hden : (0 : ℝ) < (2 * q + 1 : ℕ) := by positivity
  constructor
  · exact div_nonneg (by positivity) hden.le
  · apply (div_le_one hden).mpr
    exact_mod_cast (show j.val ≤ 2 * q + 1 by omega)

omit [DecidableEq ι] in
theorem coefficientReset_mem_ball (C : ℝ) (c v : ι → ℝ) (z : ℝ)
    (hz : z ∈ Icc (0 : ℝ) 1)
    (hc : ∑ i, |c i| ≤ C⁻¹) (hv : ∑ i, |v i| ≤ C⁻¹) :
    (∑ i, |coefficientReset c v z i|) ≤ C⁻¹ := by
  calc
    _ ≤ ∑ i, ((1 - z) * |c i| + z * |v i|) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hz.2] : 0 ≤ 1 - z), abs_of_nonneg hz.1]
    _ = (1 - z) * (∑ i, |c i|) + z * (∑ i, |v i|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 - z) * C⁻¹ + z * C⁻¹ := add_le_add
      (mul_le_mul_of_nonneg_left hc (by linarith [hz.2])) (mul_le_mul_of_nonneg_left hv hz.1)
    _ = _ := by ring

abbrev HighResponseMark (ι : Type*) (q : ℕ) := ι × ι × Bool × Bool × Fin (2 * q + 2)

/-- A genuine fixed finite atomic signed measure of coefficient resets. -/
def highResponseSignedRule (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) :
    SignedMeasure (ι → ℝ) :=
  atomicSignedRule
    (fun z : HighResponseMark ι q => coefficientReset c
      (covarianceAtom C z.1 z.2.1 z.2.2.1 z.2.2.2.1) (responseNode q z.2.2.2.2))
    (fun z : HighResponseMark ι q => covarianceWeight C A z.1 z.2.1 z.2.2.1 z.2.2.2.1 *
      responseWeight q z.2.2.2.2)

theorem highResponseSignedRule_integral (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ v, Φ v ∂<•highResponseSignedRule q C A c) = responseMatrixAction q C A c Φ := by
  rw [highResponseSignedRule, atomicSignedRule_integral]
  simp only [responseMatrixAction, covarianceAction, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem highResponseSignedRule_zero_mass (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) :
    (∫ᵛ v, (1 : ℝ) ∂<•highResponseSignedRule q C A c) = 0 := by
  rw [highResponseSignedRule_integral, responseMatrixAction_zero_mass]

theorem highResponseSignedRule_zero_mean (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (i : ι) :
    (∫ᵛ v, v i ∂<•highResponseSignedRule q C A c) = 0 := by
  rw [highResponseSignedRule_integral, responseMatrixAction_zero_mean]

theorem highResponseSignedRule_covariance (q : ℕ) (hq : 1 ≤ q) (C : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (c : ι → ℝ) (i l : ι) :
    (∫ᵛ v, v i * v l ∂<•highResponseSignedRule q C A c) = A i l := by
  rw [highResponseSignedRule_integral, responseMatrixAction_second_moment q hq C A hC hA]

theorem highResponseSignedRule_totalVariation_le (q : ℕ) (C : ℝ)
    (A : ι → ι → ℝ) (c : ι → ℝ) :
    (highResponseSignedRule q C A c).variation.real Set.univ ≤
      (2 * C ^ 2 * ∑ i, ∑ l, |A i l|) * ∑ j : Fin (2 * q + 2), |responseWeight q j| := by
  apply (atomicSignedRule_totalVariation_le _ _).trans_eq
  simp only [Fintype.sum_prod_type, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul,
    covariance_weight_variation]

theorem highResponseSignedRule_supported (q : ℕ) (C : ℝ) (hC : 0 < C)
    (A : ι → ι → ℝ) (c : ι → ℝ) (hc : ∑ i, |c i| ≤ C⁻¹) :
    (highResponseSignedRule q C A c).variation {v | ¬ (∑ i, |v i|) ≤ C⁻¹} = 0 := by
  apply atomicSignedRule_variation_outside
  · exact measurableSet_le (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).abs))
      measurable_const
  · intro z
    exact coefficientReset_mem_ball C c _ _ (responseNode_mem_unit q z.2.2.2.2) hc
      (covarianceAtom_mem_ball C hC z.1 z.2.1 z.2.2.1 z.2.2.2.1)

/-- The finite spatial polynomial frame is evaluated without any abstract
smoothness or response assumptions. -/
def spatialFrameCovariance (A : ι → ι → ℝ) {n : ℕ} (φ : Fin n → ι → ℝ)
    (i l : Fin n) : ℝ := ∑ k, ∑ m, φ i k * φ l m * A k m

def coefficientRegression {n : ℕ} (η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) : Fin n → ℝ :=
  fun i => g i + η * w i * ∑ k, φ i k * c k

def coefficientDirection {n : ℕ} (η : ℝ) (w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) : Fin n → ℝ :=
  fun i => η * w i * ∑ k, φ i k * (v k - c k)

omit [DecidableEq ι] in
theorem coefficientRegression_reset {n : ℕ} (η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) (z : ℝ) :
    coefficientRegression η g w φ (coefficientReset c v z) =
      fun i => coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i := by
  funext i
  have hs : (∑ k, φ i k * coefficientReset c v z k) =
      (∑ k, φ i k * c k) + z * ((∑ k, φ i k * v k) - ∑ k, φ i k * c k) := by
    calc
      _ = ∑ k, (φ i k * c k + z * (φ i k * v k - φ i k * c k)) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [coefficientReset]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [coefficientRegression, coefficientDirection, hs, mul_sub, Finset.sum_sub_distrib]
  ring


theorem covariance_direction_product {n : ℕ} (C η : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (i l : Fin n) :
    covarianceAction C A (fun v => coefficientDirection η w φ c v i *
      coefficientDirection η w φ c v l) = η ^ 2 * w i * w l * spatialFrameCovariance A φ i l := by
  have he : (fun v : ι → ℝ => coefficientDirection η w φ c v i * coefficientDirection η w φ c v l) =
      (fun v => η ^ 2 * w i * w l *
        ∑ k, ∑ m, (φ i k * φ l m) * ((v k - c k) * (v m - c m))) := by
    funext v
    simp only [coefficientDirection, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he, covarianceAction_mul, covarianceAction_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [covarianceAction_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [covarianceAction_mul, covariance_displacement_second C A hC hA]

/-- Real response likelihood of a single local coefficient state. -/
def highResponseProduct {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∏ i, ternaryMass a (coefficientRegression η g w φ c i) V (y i)

/-- The exact finite signed response operator is its directional Hessian
contraction through count q. This comes from actual cardinal evaluation. -/
theorem high_response_matrix_second {n : ℕ} (q : ℕ) (hn : n ≤ q)
    (C a V η : ℝ) (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      (1 / 2 : ℝ) * covarianceAction C A (fun v =>
        finiteProductSecond Finset.univ
          (fun i z => ternaryMass a (coefficientRegression η g w φ c i +
            z * coefficientDirection η w φ c v i) V (y i))
          (fun i z => coefficientDirection η w φ c v i * ternaryMeanDerivative a
            (coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i) (y i))
          (fun i _ => (coefficientDirection η w φ c v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0) := by
  rw [← covarianceAction_mul]
  apply congrArg (covarianceAction C A)
  funext v
  simp only [highResponseProduct, coefficientRegression_reset]
  rw [response_line_rule_exact q n a V _ _ y hn]
  have h := response_line_quadratic_coefficient n a V
    (coefficientRegression η g w φ c) (coefficientDirection η w φ c v) y
  linarith

/-- The variance derivative before substituting a common variance. -/
def highResponseVarianceTerm {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) * ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
    ternaryMass a (coefficientRegression η g w φ c l) V (y l)

omit [DecidableEq ι] in
theorem high_response_variance_hasDerivAt {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) :
    HasDerivAt (fun W => highResponseProduct a W η g w φ c y)
      (∑ i, highResponseVarianceTerm a V η g w φ c y i) V := by
  simpa only [highResponseProduct, highResponseVarianceTerm, smul_eq_mul, mul_comm] using
    HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
      (fun i _ => ternary_hasDerivAt_variance a (coefficientRegression η g w φ c i) V (y i))

/-- Spatial cardinal covariance cancels every off-diagonal product derivative.
This is the actual heat identity of the realized finite signed update. -/
theorem high_response_matrix_heat {n : ℕ} (q : ℕ) (hn : n ≤ q)
    (C a V η : ℝ) (A : ι → ι → ℝ) (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (d : Fin n → ℝ)
    (hdiag : ∀ i l, spatialFrameCovariance A φ i l = if i = l then d i else 0) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
  let f := coefficientRegression η g w φ c
  let δ := coefficientDirection η w φ c
  let p := fun i => ternaryMass a (f i) V (y i)
  let m := fun i => ternaryMeanDerivative a (f i) (y i)
  let e := fun i => ternaryMeanSecondDerivative a (y i)
  let S : (ι → ℝ) → ℝ := fun v => ∑ i : Fin n,
    ((∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
      (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) *
        m l * m i * (δ v l * δ v i)) +
      (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, p l) * e i * (δ v i * δ v i))
  have hS (v : ι → ℝ) :
      finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
        (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
        (fun i _ => (δ v i) ^ 2 * e i) 0 = S v := by
    simp only [finiteProductSecond, zero_mul, add_zero, S]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      dsimp [p, m]
      ring
    · dsimp [p]
      ring
  rw [high_response_matrix_second q hn C a V η A g w φ c y]
  change (1 / 2 : ℝ) * covarianceAction C A
    (fun v => finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * e i) 0) = _
  simp_rw [hS]
  unfold S
  rw [covarianceAction_sum]
  have he (i : Fin n) : covarianceAction C A
      (fun v => (∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
        (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) *
          m l * m i * (δ v l * δ v i)) +
        (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, p l) * e i * (δ v i * δ v i)) =
      2 * η ^ 2 * (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
    rw [covarianceAction_add, covarianceAction_sum]
    have hcross (l : Fin n) (hl : l ∈ (Finset.univ : Finset (Fin n)).erase i) :
        covarianceAction C A (fun v =>
          (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) * m l * m i *
            (δ v l * δ v i)) = 0 := by
      rw [covarianceAction_mul, covariance_direction_product C η A hC hA w φ c l i,
        hdiag l i, ite_eq_right (Finset.ne_of_mem_erase hl), mul_zero, mul_zero]
    rw [Finset.sum_eq_zero (fun l hl => hcross l hl), zero_add, covarianceAction_mul,
      covariance_direction_product C η A hC hA w φ c i i, hdiag i i, ite_eq_left rfl]
    dsimp [e, highResponseVarianceTerm]
    rw [ternary_heat_identity]
    dsimp [p, f]
    ring
  simp_rw [he]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All-count cardinal action bound propagated through the genuine product
likelihood. The assumptions are individual legality and displacement bounds. -/
theorem response_scalar_product_action_abs_bound (q n : ℕ) (hn : 1 ≤ n)
    (a V η ρ : ℝ) (f δ : Fin n → ℝ) (y : Fin n → Fin 3)
    (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hf : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i, |f i + z * δ i| ≤ ρ)
    (hp : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i u, 0 ≤ ternaryMass a (f i + z * δ i) V u)
    (hδ : ∀ i, |δ i| ≤ 2 * η) :
    |∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
        (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2) := by
  let H : Fin n → ℝ → ℝ := fun i z => ternaryMass a (f i + z * δ i) V (y i)
  let D : Fin n → ℝ → ℝ := fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)
  let A := (2 * ρ + a) / a ^ 2
  let S := 2 / a ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hH (i : Fin n) (z : ℝ) : HasDerivAt (H i) (D i z) z := by
    have h := (ternary_hasDerivAt_mean a (f i + z * δ i) V (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))
    exact h.congr_deriv (by dsimp [D]; ring)
  have hD (i : Fin n) (z : ℝ) : HasDerivAt (D i) (E i z) z := by
    have h := ((ternary_hasDerivAt_mean_derivative a (f i + z * δ i) (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))).const_mul (δ i)
    exact h.congr_deriv (by dsimp [E]; ring)
  have hHbound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |H i z| ≤ 1 := by
    rw [abs_of_nonneg (hp z hz i (y i))]
    exact ternary_mass_le_one a _ V ha.ne' (hp z hz i) (y i)
  have hDbound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |D i z| ≤ 2 * η * A := by
    rw [abs_mul]
    exact mul_le_mul (hδ i) (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf z hz i) (y i))
      (abs_nonneg _) (by positivity)
  have hEbound (z : ℝ) (i : Fin n) : |E i z| ≤ 4 * η ^ 2 * S := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hs : (δ i) ^ 2 ≤ (2 * η) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2
    have h := mul_le_mul hs (ternary_mean_second_derivative_abs_bound a ha (y i))
      (abs_nonneg _) (by positivity : 0 ≤ (2 * η) ^ 2)
    simpa only [S] using h.trans_eq (by ring)
  apply response_scalar_action_abs_bound q _ (finiteProductFirst Finset.univ H D)
    (finiteProductSecond Finset.univ H D E) _ (by positivity)
    (fun z hz => finite_product_hasDerivAt Finset.univ H D z (fun i _ => hH i z))
    (fun z hz => finite_product_first_hasDerivAt Finset.univ H D E z
      (fun i _ => hH i z) (fun i _ => hD i z)) _ (responseNode_mem_unit q)
  intro z hz
  have h := finite_product_second_abs_bound Finset.univ H D E z (2 * η * A) (4 * η ^ 2 * S)
    (by positivity) (by positivity) (fun i _ => hHbound z hz i)
    (fun i _ => hDbound z hz i) (fun i _ => hEbound z i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) ^ 2 - n := by nlinarith
  have hmore := mul_nonneg hnn (mul_nonneg (sq_nonneg η) hS)
  dsimp [A, S] at *
  nlinarith

/-- Matrix-response bound at every count, derived from legal frame resets
and the actual ternary product derivatives. -/
theorem high_response_matrix_all_count_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ / 2) (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2)
    (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    |responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y)| ≤
      (2 * C ^ 2 * ∑ k, ∑ l, |A k l|) *
        ((∑ j : Fin (2 * q + 2), |responseWeight q j|) *
          (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2)) := by
  unfold responseMatrixAction
  apply covarianceAction_abs_le
  intro k l s t
  let v := covarianceAtom C k l s t
  have hv : (∑ k, |v k|) ≤ C⁻¹ := covarianceAtom_mem_ball C hC k l s t
  let f := coefficientRegression η g w φ c
  let δ := coefficientDirection η w φ c v
  have hr (z : ℝ) : coefficientRegression η g w φ (coefficientReset c v z) =
      fun i => f i + z * δ i := coefficientRegression_reset η g w φ c v z
  have hδ (i : Fin n) : |δ i| ≤ 2 * η := by
    have hprof : |∑ k, φ i k * (v k - c k)| ≤ 2 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact (abs_sub _ _).trans (by linarith [hφ v hv i, hφ c hc i])
    have hm : |η * w i| ≤ η := by
      rw [abs_mul, abs_of_nonneg hη]
      exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one η)
    change |η * w i * (∑ k, φ i k * (v k - c k))| ≤ 2 * η
    rw [abs_mul]
    exact (mul_le_mul hm hprof (abs_nonneg _) hη).trans_eq (by ring)
  have hf (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |f i + z * δ i| ≤ ρ := by
    have hi := congrFun (hr z) i
    rw [← hi]
    have hball := coefficientReset_mem_ball C c v z hz hc hv
    have hprof := hφ _ hball i
    change |g i + η * w i * (∑ k, φ i k * coefficientReset c v z k)| ≤ ρ
    have hm : |η * w i| ≤ η := by
      rw [abs_mul, abs_of_nonneg hη]
      exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one η)
    have hpterm : |η * w i * (∑ k, φ i k * coefficientReset c v z k)| ≤ η := by
      rw [abs_mul]
      exact (mul_le_mul hm hprof (abs_nonneg _) hη).trans_eq (mul_one η)
    exact (abs_add_le _ _).trans (by linarith [hg i, hpterm])
  have he : (∑ j : Fin (2 * q + 2), responseWeight q j *
      highResponseProduct a V η g w φ (coefficientReset c v (responseNode q j)) y) =
      ∑ j : Fin (2 * q + 2), responseWeight q j *
        ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i) := by
    simp only [highResponseProduct, hr]
  rw [he]
  exact response_scalar_product_action_abs_bound q n hn a V η ρ f δ y ha hη hρ hf
    (fun z hz i u => hp _ (hf z hz i) u) hδ

end Covariance

end NearlyMinimax
