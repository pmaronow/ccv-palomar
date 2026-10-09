module

public import NearlyMinimax.HighResponseRemainder


@[expose] public section

/-! Actual finite density-marked response updates and their local scores.
All likelihood and score bounds are proved from legal density/response
factors and the finite atomic rules. -/
noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

section Packet
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

/-- Density marks are kept separate from the response covariance marks. -/
def highDensityResponseAction (q : ℕ) (C : ℝ) (weights : E → ℝ)
    (A : E → ι → ι → ℝ) (c : ι → ℝ) (b : E → ℝ)
    (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∑ e, weights e * b e * responseMatrixAction q C (A e) c Φ

theorem high_density_response_zero_mass (q : ℕ) (C : ℝ) (weights : E → ℝ)
    (A : E → ι → ι → ℝ) (c : ι → ℝ) (b : E → ℝ) :
    highDensityResponseAction q C weights A c b (fun _ => 1) = 0 := by
  simp only [highDensityResponseAction, responseMatrixAction_zero_mass, mul_zero, Finset.sum_const_zero]

/-- Conditional first-moment annihilation for every density observable. -/
theorem high_density_response_zero_mean (q : ℕ) (C : ℝ) (weights : E → ℝ)
    (A : E → ι → ι → ℝ) (c : ι → ℝ) (b : E → ℝ) (i : ι) :
    highDensityResponseAction q C weights A c b (fun v => v i) = 0 := by
  simp only [highDensityResponseAction, responseMatrixAction_zero_mean, mul_zero, Finset.sum_const_zero]

/-- A genuine finite signed density-response packet, on reset density
values and reset coefficients. -/
def highDensityResponseSignedPacket {n : ℕ} (q : ℕ) (C : ℝ) (weights : E → ℝ)
    (A : E → ι → ι → ℝ) (c : ι → ℝ) (pReset : E → Fin n → ℝ) :
    SignedMeasure ((Fin n → ℝ) × (ι → ℝ)) :=
  atomicSignedRule
    (fun z : E × HighResponseMark ι q => (pReset z.1,
      coefficientReset c
        (covarianceAtom C z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1)
        (responseNode q z.2.2.2.2.2)))
    (fun z : E × HighResponseMark ι q => weights z.1 *
      (covarianceWeight C (A z.1) z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 *
        responseWeight q z.2.2.2.2.2))

theorem highDensityResponseSignedPacket_integral {n : ℕ} (q : ℕ) (C : ℝ)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (c : ι → ℝ)
    (pReset : E → Fin n → ℝ) (b : (Fin n → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ z, b z.1 * Φ z.2 ∂<•highDensityResponseSignedPacket q C weights A c pReset) =
      highDensityResponseAction q C weights A c (fun e => b (pReset e)) Φ := by
  rw [highDensityResponseSignedPacket, atomicSignedRule_integral]
  simp only [highDensityResponseAction, responseMatrixAction, covarianceAction,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The packet's weak conditional annihilation holds for every actual
density observable, with no assumption on that observable's values. -/
theorem highDensityResponseSignedPacket_conditional_annihilation {n : ℕ}
    (q : ℕ) (C : ℝ) (weights : E → ℝ) (A : E → ι → ι → ℝ)
    (c : ι → ℝ) (pReset : E → Fin n → ℝ) (b : (Fin n → ℝ) → ℝ) (i : ι) :
    (∫ᵛ z, b z.1 ∂<•highDensityResponseSignedPacket q C weights A c pReset) = 0 ∧
    (∫ᵛ z, b z.1 * z.2 i ∂<•highDensityResponseSignedPacket q C weights A c pReset) = 0 := by
  constructor
  · have h := highDensityResponseSignedPacket_integral q C weights A c pReset b (fun _ => 1)
    simpa only [mul_one, high_density_response_zero_mass] using h
  · have h := highDensityResponseSignedPacket_integral q C weights A c pReset b (fun v => v i)
    simpa only [high_density_response_zero_mean] using h

omit [DecidableEq ι] in
theorem high_response_product_normalized {n : ℕ} (a V η : ℝ) (ha : a ≠ 0)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) :
    ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y = 1 := by
  unfold highResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

omit [DecidableEq ι] in
theorem high_response_variance_term_sum_zero {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (i : Fin n) :
    ∑ y : Fin n → Fin 3, highResponseVarianceTerm a V η g w φ c y i = 0 := by
  simpa only [highResponseVarianceTerm, patchVarianceTerm, zero_mul, add_zero] using
    patch_variance_term_sum_zero n a V 0 (coefficientRegression η g w φ c) (fun _ => 0) 0 i

/-- The local derivative remainder numerator of the actual marked
response packet and the variance path. -/
def highLocalScoreNumerator {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  highDensityResponseAction q C weights A c (fun e => ∏ i, pReset e i)
    (fun c => highResponseProduct a V η g w φ c y) -
  η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i

def highLocalScore {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  highLocalScoreNumerator q C a V η weights A p pReset g w φ c y /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)

/-- Summing over actual response labels kills both the packet and the
variance derivative; no conditional mean premise is needed. -/
theorem high_local_score_numerator_sum_zero {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (ha : a ≠ 0) (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) :
    ∑ y : Fin n → Fin 3, highLocalScoreNumerator q C a V η weights A p pReset g w φ c y = 0 := by
  unfold highLocalScoreNumerator highDensityResponseAction
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have hfirst (e : E) :
      (∑ y : Fin n → Fin 3, weights e * (∏ i, pReset e i) *
        responseMatrixAction q C (A e) c (fun c => highResponseProduct a V η g w φ c y)) = 0 := by
    rw [← Finset.mul_sum, ← responseMatrixAction_sum]
    simp only [high_response_product_normalized a V η ha g w φ,
      responseMatrixAction_zero_mass, mul_zero]
  rw [Finset.sum_eq_zero (fun e _ => hfirst e), ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, high_response_variance_term_sum_zero, mul_zero,
    Finset.sum_const_zero, sub_zero]

/-- Exact conditional centering of the true normalized local score. -/
theorem high_local_score_centered {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (ha : a ≠ 0) (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (hresponse : ∀ y, highResponseProduct a V η g w φ c y ≠ 0) :
    ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y *
      highLocalScore q C a V η weights A p pReset g w φ c y = 0 := by
  have hp0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have he (y : Fin n → Fin 3) : highResponseProduct a V η g w φ c y *
      highLocalScore q C a V η weights A p pReset g w φ c y =
      highLocalScoreNumerator q C a V η weights A p pReset g w φ c y / (∏ i, p i) := by
    unfold highLocalScore
    field_simp [hp0, hresponse y]
  simp_rw [he]
  rw [← Finset.sum_div, high_local_score_numerator_sum_zero q C a V η ha]
  exact zero_div _

/-- The explicit finite covariance-mark variation entering the response
packet; it is determined by the actual matrices and density weights. -/
def highResponsePacketCost (C : ℝ) (weights : E → ℝ) (A : E → ι → ι → ℝ) : ℝ :=
  ∑ e, |weights e| * (2 * C ^ 2 * ∑ k, ∑ l, |A e k l|)

def highLocalDerivativeConstant (q : ℕ) (a ρ : ℝ) : ℝ :=
  (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
    (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2))

def highLocalScoreConstant (q : ℕ) (C a ρ : ℝ)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) : ℝ :=
  highResponsePacketCost C weights A * highLocalDerivativeConstant q a ρ + 1 / a ^ 2

theorem highDensityResponseSignedPacket_totalVariation_le {n : ℕ}
    (q : ℕ) (C : ℝ) (weights : E → ℝ) (A : E → ι → ι → ℝ)
    (c : ι → ℝ) (pReset : E → Fin n → ℝ) :
    (highDensityResponseSignedPacket q C weights A c pReset).variation.real Set.univ ≤
      highResponsePacketCost C weights A *
        ∑ j : Fin (2 * q + 2), |responseWeight q j| := by
  apply (atomicSignedRule_totalVariation_le _ _).trans_eq
  simp only [Fintype.sum_prod_type, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [covariance_weight_variation, highResponsePacketCost, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem highDensityResponseSignedPacket_coefficient_support {n : ℕ}
    (q : ℕ) (C : ℝ) (hC : 0 < C) (weights : E → ℝ) (A : E → ι → ι → ℝ)
    (c : ι → ℝ) (hc : ∑ k, |c k| ≤ C⁻¹) (pReset : E → Fin n → ℝ) :
    (highDensityResponseSignedPacket q C weights A c pReset).variation
      {z | ¬ (∑ k, |z.2 k|) ≤ C⁻¹} = 0 := by
  apply atomicSignedRule_variation_outside
  · exact measurableSet_le
      (Finset.measurable_sum _ (fun k _ => ((measurable_pi_apply k).comp measurable_snd).abs))
      measurable_const
  · intro z
    exact coefficientReset_mem_ball C c _ _ (responseNode_mem_unit q z.2.2.2.2.2) hc
      (covarianceAtom_mem_ball C hC z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1)

theorem finite_density_product_abs_bound {n : ℕ} (p : Fin n → ℝ) (pPlus : ℝ)
    (_hpPlus : 0 ≤ pPlus) (hp : ∀ i, |p i| ≤ pPlus) :
    |∏ i, p i| ≤ pPlus ^ n := by
  rw [Finset.abs_prod]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => abs_nonneg (p i))
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)

omit [DecidableEq ι] in
theorem high_response_variance_term_abs_bound {n : ℕ} (a V η : ℝ) (ha : 0 < a)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) (i : Fin n) :
    |highResponseVarianceTerm a V η g w φ c y i| ≤ 1 / a ^ 2 := by
  have hprod : |∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (coefficientRegression η g w φ c l) V (y l)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply (Finset.prod_le_prod₀ (fun l _ => abs_nonneg _)
      (fun l _ => show |ternaryMass a (coefficientRegression η g w φ c l) V (y l)| ≤ 1 from by
        rw [abs_of_nonneg (hp l (y l))]
        exact ternary_mass_le_one a _ V ha.ne' (hp l) (y l))).trans_eq
    exact Finset.prod_const_one
  unfold highResponseVarianceTerm
  rw [abs_mul]
  exact (mul_le_mul (ternary_variance_derivative_abs_bound a ha (y i)) hprod
    (abs_nonneg _) (by positivity : 0 ≤ 1 / a ^ 2)).trans_eq (mul_one _)

theorem high_density_response_product_abs_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (pReset : E → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (y : Fin n → Fin 3) :
    |highDensityResponseAction q C weights A c (fun e => ∏ i, pReset e i)
      (fun c => highResponseProduct a V η g w φ c y)| ≤
      pPlus ^ n * highResponsePacketCost C weights A *
        (highLocalDerivativeConstant q a ρ * (n : ℝ) ^ 2 * η ^ 2) := by
  unfold highDensityResponseAction
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e, (|weights e| * pPlus ^ n) *
        ((2 * C ^ 2 * ∑ k, ∑ l, |A e k l|) *
          (highLocalDerivativeConstant q a ρ * (n : ℝ) ^ 2 * η ^ 2)) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul, abs_mul]
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left
          (finite_density_product_abs_bound (pReset e) pPlus hpPlus (hReset e)) (abs_nonneg _))
        _ (abs_nonneg _) (by positivity)
      exact (high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
        (A e) g w φ c y hc hg hw hφ hp).trans_eq (by
          unfold highLocalDerivativeConstant
          ring)
    _ = _ := by
      unfold highResponsePacketCost
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring

theorem high_local_score_numerator_abs_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (y : Fin n → Fin 3) :
    |highLocalScoreNumerator q C a V η weights A p pReset g w φ c y| ≤
      pPlus ^ n * highLocalScoreConstant q C a ρ weights A * (n : ℝ) ^ 2 * η ^ 2 := by
  have hfield (i : Fin n) : |coefficientRegression η g w φ c i| ≤ ρ := by
    simpa only [zero_mul, add_zero] using
      coefficient_regression_reset_abs_le C η ρ hη hηρ g w φ c c 0 (by norm_num)
        hc hc hg hw hφ i
  have hvar : |∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      (n : ℝ) / a ^ 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hwsq : (w i) ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2
        exact (mul_le_mul hwsq
          (high_response_variance_term_abs_bound a V η ha g w φ c
            (fun i u => hp _ (hfield i) u) y i)
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  have hvariance : |η ^ 2 * (∏ i, p i) *
      ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      η ^ 2 * pPlus ^ n * ((n : ℝ) / a ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (finite_density_product_abs_bound p pPlus hpPlus hIncoming) (sq_nonneg η))
      hvar (abs_nonneg _) (by positivity)
  unfold highLocalScoreNumerator
  apply (abs_sub _ _).trans
  apply (add_le_add
    (high_density_response_product_abs_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
      weights A pReset g w φ c hc hg hw hφ hp hReset y) hvariance).trans
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmore : 0 ≤ pPlus ^ n * η ^ 2 / a ^ 2 * ((n : ℝ) ^ 2 - n) := by
    apply mul_nonneg (by positivity)
    nlinarith
  unfold highLocalScoreConstant
  apply sub_nonneg.mp
  convert hmore using 1; ring

theorem high_local_score_abs_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus pMinus cMass : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hIncomingLower : ∀ i, pMinus ≤ p i)
    (hResponseLower : ∀ i u, cMass ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) :
    |highLocalScore q C a V η weights A p pReset g w φ c y| ≤
      (pPlus / (pMinus * cMass)) ^ n *
        highLocalScoreConstant q C a ρ weights A * (n : ℝ) ^ 2 * η ^ 2 := by
  have hp0 (i : Fin n) : 0 < p i := hpMinus.trans_le (hIncomingLower i)
  have hq0 (i : Fin n) : 0 < ternaryMass a (coefficientRegression η g w φ c i) V (y i) :=
    hcMass.trans_le (hResponseLower i (y i))
  have hP0 : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => hp0 i)
  have hH0 : 0 < highResponseProduct a V η g w φ c y :=
    Finset.prod_pos (fun i _ => hq0 i)
  have hden0 : 0 < (∏ i, p i) * highResponseProduct a V η g w φ c y := mul_pos hP0 hH0
  have hPLower : pMinus ^ n ≤ ∏ i, p i := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hpMinus.le)
        (fun i _ => hIncomingLower i)
  have hHLower : cMass ^ n ≤ highResponseProduct a V η g w φ c y := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, highResponseProduct] using
      Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hcMass.le)
        (fun i _ => hResponseLower i (y i))
  have hdenLower : (pMinus * cMass) ^ n ≤
      (∏ i, p i) * highResponseProduct a V η g w φ c y := by
    rw [mul_pow]
    exact mul_le_mul hPLower hHLower (pow_nonneg hcMass.le _) hP0.le
  have hdenLower0 : 0 < (pMinus * cMass) ^ n := pow_pos (mul_pos hpMinus hcMass) _
  have hK0 : 0 ≤ highLocalScoreConstant q C a ρ weights A := by
    unfold highLocalScoreConstant highResponsePacketCost highLocalDerivativeConstant
    positivity
  have hN := high_local_score_numerator_abs_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
    weights A p pReset g w φ c hc hg hw hφ hp hReset hIncoming y
  unfold highLocalScore
  rw [abs_div, abs_of_nonneg hden0.le]
  calc
    _ ≤ (pPlus ^ n * highLocalScoreConstant q C a ρ weights A * (n : ℝ) ^ 2 * η ^ 2) /
        ((∏ i, p i) * highResponseProduct a V η g w φ c y) :=
      div_le_div_of_nonneg_right hN hden0.le
    _ ≤ (pPlus ^ n * highLocalScoreConstant q C a ρ weights A * (n : ℝ) ^ 2 * η ^ 2) /
        ((pMinus * cMass) ^ n) :=
      div_le_div_of_nonneg_left (by positivity) hdenLower0 hdenLower
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- Conditional square-energy of the true finite-packet score, derived
at every count from the actual update and likelihood margins. -/
theorem high_local_score_energy_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus pMinus cMass : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hIncomingLower : ∀ i, pMinus ≤ p i)
    (hResponseLower : ∀ i u, cMass ≤ ternaryMass a (coefficientRegression η g w φ c i) V u) :
    (∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y *
      (highLocalScore q C a V η weights A p pReset g w φ c y) ^ 2) ≤
      (pPlus / (pMinus * cMass)) ^ (2 * n) *
        (highLocalScoreConstant q C a ρ weights A) ^ 2 * (n : ℝ) ^ 4 * η ^ 4 := by
  let B := (pPlus / (pMinus * cMass)) ^ n *
    highLocalScoreConstant q C a ρ weights A * (n : ℝ) ^ 2 * η ^ 2
  have hbound (y : Fin n → Fin 3) : |highLocalScore q C a V η weights A p pReset g w φ c y| ≤ B :=
    high_local_score_abs_bound q hn C a V η ρ pPlus pMinus cMass hC ha hη hρ hηρ hpPlus
      hpMinus hcMass weights A p pReset g w φ c hc hg hw hφ hp hReset hIncoming
      hIncomingLower hResponseLower y
  have hB0 : 0 ≤ B := by
    unfold B highLocalScoreConstant highResponsePacketCost highLocalDerivativeConstant
    positivity
  calc
    _ ≤ ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y * B ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _
        (Finset.prod_nonneg (fun i _ => (hcMass.trans_le (hResponseLower i (y i))).le))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound y) 2
    _ = B ^ 2 := by rw [← Finset.sum_mul, high_response_product_normalized a V η ha.ne', one_mul]
    _ = _ := by
      dsimp [B]
      simp only [mul_pow, ← pow_mul]
      congr 3
      rw [Nat.mul_comm n 2]

end Packet
end NearlyMinimax
