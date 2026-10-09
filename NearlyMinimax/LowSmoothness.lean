module

public import NearlyMinimax.Ternary


@[expose] public section

/-! # Finite low-smoothness experiment

This file constructs the activation prior and finite conditional response
likelihood used in the paper's small-smoothness lower bound. It proves the
prior derivative, the exact zero/one-observation cancellation, and centering
of the observable score. All expectations below are actual finite sums.
-/

namespace NearlyMinimax

noncomputable section

/-- The prior `(t/2, 1-t, t/2)` on the latent values `(-1,0,1)`. -/
def activationPriorMass (t : ℝ) : Fin 3 → ℝ := ![t / 2, 1 - t, t / 2]

/-- Its signed derivative, `(1/2,-1,1/2)`. -/
def activationPriorDerivative : Fin 3 → ℝ := ![(1 / 2 : ℝ), -1, 1 / 2]

theorem activation_prior_normalized (t : ℝ) : ∑ y, activationPriorMass t y = 1 := by
  simp [Fin.sum_univ_succ, activationPriorMass]
  ring

theorem activation_prior_nonnegative (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ y, 0 ≤ activationPriorMass t y := by
  intro y
  fin_cases y <;> simp [activationPriorMass] <;> linarith

theorem activation_prior_hasDerivAt (t : ℝ) (y : Fin 3) :
    HasDerivAt (fun u => activationPriorMass u y) (activationPriorDerivative y) t := by
  fin_cases y
  · exact (hasDerivAt_id t).div_const 2
  · change HasDerivAt (fun u => 1 - u) (-1) t
    exact ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).congr_deriv (by norm_num)
  · exact (hasDerivAt_id t).div_const 2

/-- The independent activation prior on `m` latent coordinates. -/
def activationProductPrior (m : ℕ) (t : ℝ) (ξ : Fin m → Fin 3) : ℝ :=
  ∏ j, activationPriorMass t (ξ j)

/-- Differentiating the product replaces one factor by its signed derivative. -/
def activationProductPriorDerivative (m : ℕ) (t : ℝ) (ξ : Fin m → Fin 3) : ℝ :=
  ∑ j, activationPriorDerivative (ξ j) *
    ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)

theorem activation_product_prior_normalized (m : ℕ) (t : ℝ) :
    ∑ ξ, activationProductPrior m t ξ = 1 := by
  unfold activationProductPrior
  rw [← Fintype.prod_sum]
  simp [activation_prior_normalized]

theorem activation_product_prior_hasDerivAt (m : ℕ) (t : ℝ) (ξ : Fin m → Fin 3) :
    HasDerivAt (fun u => activationProductPrior m u ξ)
      (activationProductPriorDerivative m t ξ) t := by
  have h := HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset (Fin m)))
    (fun j _ => activation_prior_hasDerivAt t (ξ j))
  simpa [activationProductPrior, activationProductPriorDerivative, smul_eq_mul,
    mul_comm] using h

/-- A finite expectation under the product activation prior. -/
def activationExpectation (m : ℕ) (t : ℝ) (F : ℝ → (Fin m → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ * F t ξ

/-- The finite-mixture derivative includes both prior and observable derivatives. -/
theorem activation_expectation_hasDerivAt (m : ℕ) (t : ℝ)
    (F : ℝ → (Fin m → Fin 3) → ℝ) (dF : (Fin m → Fin 3) → ℝ)
    (hF : ∀ ξ, HasDerivAt (fun u => F u ξ) (dF ξ) t) :
    HasDerivAt (fun u => activationExpectation m u F)
      (∑ ξ : (Fin m → Fin 3), (activationProductPriorDerivative m t ξ * F t ξ +
        activationProductPrior m t ξ * dF ξ)) t := by
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m → Fin 3)))
    (fun ξ _ =>
    (activation_product_prior_hasDerivAt m t ξ).mul (hF ξ))

/-- The coordinate replacement operator `D_j` in the paper. -/
def latentDifference (m : ℕ) (j : Fin m) (F : (Fin m → Fin 3) → ℝ)
    (ξ : Fin m → Fin 3) : ℝ :=
  (1 / 2 : ℝ) * F (Function.update ξ j 2) +
    (1 / 2 : ℝ) * F (Function.update ξ j 0) - F (Function.update ξ j 1)

/-- Replacement is integration against the signed derivative of the prior. -/
theorem latent_difference_eq_signed_sum (m : ℕ) (j : Fin m)
    (F : (Fin m → Fin 3) → ℝ) (ξ : Fin m → Fin 3) :
    latentDifference m j F ξ =
      ∑ z : Fin 3, activationPriorDerivative z * F (Function.update ξ j z) := by
  simp [latentDifference, Fin.sum_univ_succ, activationPriorDerivative]
  ring

theorem latent_difference_const (m : ℕ) (j : Fin m) (c : ℝ) (ξ : Fin m → Fin 3) :
    latentDifference m j (fun _ => c) ξ = 0 := by
  unfold latentDifference
  ring

private theorem activation_prior_factor (m : ℕ) (t : ℝ) (ξ : Fin m → Fin 3) (j : Fin m) :
    activationProductPrior m t ξ = activationPriorMass t (ξ j) *
      ∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k) := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

private theorem activation_coordinate_sum (m : ℕ) (t : ℝ) (j : Fin m)
    (r : Fin 3 → ℝ) (F : (Fin m → Fin 3) → ℝ) :
    (∑ ξ : Fin m → Fin 3, r (ξ j) *
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)) * F ξ) =
      ∑ u : ({k : Fin m // k ≠ j} → Fin 3),
        (∏ k : {k : Fin m // k ≠ j}, activationPriorMass t (u k)) *
          ∑ z : Fin 3, r z * F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) := by
  have hrest (z : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j,
        activationPriorMass t ((Equiv.funSplitAt j (Fin 3)).symm (z, u) k)) =
        ∏ k : {k : Fin m // k ≠ j}, activationPriorMass t (u k) := by
    rw [Finset.prod_subtype (p := fun k : Fin m => k ≠ j) _ (by simp [eq_comm])]
    apply Finset.prod_congr rfl
    intro k _
    simp [Equiv.funSplitAt_symm_apply, k.property]
  rw [← (Equiv.funSplitAt j (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [hrest]
  simp only [Equiv.funSplitAt_symm_apply, dite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Differentiation of a coordinate prior is the weighted expectation of
its replacement operator, with no division by a possibly zero prior mass. -/
theorem activation_coordinate_replacement (m : ℕ) (t : ℝ) (j : Fin m)
    (F : (Fin m → Fin 3) → ℝ) :
    (∑ ξ : Fin m → Fin 3, activationPriorDerivative (ξ j) *
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)) * F ξ) =
      ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ * latentDifference m j F ξ := by
  have hupdate (z z' : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
      Function.update ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) j z' =
        (Equiv.funSplitAt j (Fin 3)).symm (z', u) := by
    funext k
    by_cases h : k = j
    · subst k
      simp [Equiv.funSplitAt_symm_apply]
    · simp [Equiv.funSplitAt_symm_apply, h]
  have hD (z : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
      latentDifference m j F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) =
        ∑ z' : Fin 3, activationPriorDerivative z' *
          F ((Equiv.funSplitAt j (Fin 3)).symm (z', u)) := by
    rw [latent_difference_eq_signed_sum]
    simp_rw [hupdate]
  simp_rw [activation_prior_factor m t _ j]
  rw [activation_coordinate_sum m t j activationPriorDerivative F,
    activation_coordinate_sum m t j (activationPriorMass t) (latentDifference m j F)]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [hD]
  rw [← Finset.sum_mul, activation_prior_normalized]
  simp

/-- The full prior derivative is represented by the sum of observable
coordinate replacements. -/
theorem activation_prior_derivative_replacement (m : ℕ) (t : ℝ)
    (F : (Fin m → Fin 3) → ℝ) :
    (∑ ξ : Fin m → Fin 3, activationProductPriorDerivative m t ξ * F ξ) =
      ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ * ∑ j, latentDifference m j F ξ := by
  unfold activationProductPriorDerivative
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact activation_coordinate_replacement m t j F

/-- Actual derivative of an expectation of a fixed observable under the
activation prior, in the replacement representation used by the paper. -/
theorem activation_fixed_expectation_hasDerivAt (m : ℕ) (t : ℝ)
    (F : (Fin m → Fin 3) → ℝ) :
    HasDerivAt (fun u => ∑ ξ : Fin m → Fin 3, activationProductPrior m u ξ * F ξ)
      (∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ * ∑ j, latentDifference m j F ξ) t := by
  rw [← activation_prior_derivative_replacement]
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m → Fin 3)))
    (fun ξ _ => (activation_product_prior_hasDerivAt m t ξ).mul_const (F ξ))

/-- Symmetric replacement of one real latent coordinate by `+1,-1,0`. -/
def symmetricDifference (H : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * H 1 + (1 / 2 : ℝ) * H (-1) - H 0

/-- Response likelihood of one patch, with all other latent coordinates
absorbed into the regression vector `g`. -/
def patchResponseProduct (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  ∏ i, ternaryMass a (g i + η * w i * z) V (y i)

/-- Differentiation in the variance of observation `i` only. -/
def patchVarianceTerm (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (g k + η * w k * z) V (y k)

/-- The numerator of the observable patch score in equation (small-s-score). -/
def patchScoreNumerator (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  symmetricDifference (patchResponseProduct n a V η g w y) -
    η ^ 2 * ∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i

/-- The observable patch score itself. -/
def patchObservableScore (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) : ℝ :=
  patchScoreNumerator n a V η g w y z / patchResponseProduct n a V η g w y z

/-- Each conditional sample likelihood sums to one. -/
theorem patch_response_normalized (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (z : ℝ) (ha : a ≠ 0) :
    ∑ y, patchResponseProduct n a V η g w y z = 1 := by
  unfold patchResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

private theorem patch_product_singleton (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (i : Fin n) (hw : ∀ k, k ≠ i → w k = 0) :
    patchResponseProduct n a V η g w y z =
      ternaryMass a (g i + η * w i * z) V (y i) *
        ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (g k) V (y k) := by
  unfold patchResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [hw k (Finset.ne_of_mem_erase hk)]
  simp

/-- A patch containing no effective observation has zero score numerator. -/
theorem patch_score_cancel_zero (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (hw : ∀ i, w i = 0) :
    patchScoreNumerator n a V η g w y z = 0 := by
  simp [patchScoreNumerator, symmetricDifference, patchResponseProduct, hw]
  ring

/-- The exact heat cancellation for a patch containing at most one effective
observation. It holds for every current value `z` of the latent coordinate. -/
theorem patch_score_cancel_singleton (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (ha : a ≠ 0) (i : Fin n)
    (hw : ∀ k, k ≠ i → w k = 0) :
    patchScoreNumerator n a V η g w y z = 0 := by
  have hterm : ∑ k, (w k) ^ 2 * patchVarianceTerm n a V η g w y z k =
      (w i) ^ 2 * patchVarianceTerm n a V η g w y z i := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      simp [hw k hki]
    · simp
  have hvar : patchVarianceTerm n a V η g w y z i =
      ternaryVarianceDerivative a (y i) *
        ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (g k) V (y k) := by
    unfold patchVarianceTerm
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    simp [hw k (Finset.ne_of_mem_erase hk)]
  unfold patchScoreNumerator symmetricDifference
  rw [hterm, hvar, patch_product_singleton n a V η g w y 1 i hw,
    patch_product_singleton n a V η g w y (-1) i hw,
    patch_product_singleton n a V η g w y 0 i hw]
  simp only [mul_one, mul_neg_one, mul_zero, add_zero]
  have hheat := ternary_finite_difference a (g i) V η (w i) ha (y i)
  simp only [sub_eq_add_neg] at hheat
  linear_combination (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
    ternaryMass a (g k) V (y k)) * hheat

/-- The partial-variance term is an actual derivative of the product
likelihood with only observation `i`'s variance varied. -/
theorem patch_variance_term_hasDerivAt (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (i : Fin n) :
    HasDerivAt (fun W => ∏ k : Fin n,
      ternaryMass a (g k + η * w k * z) (if k = i then W else V) (y k))
      (patchVarianceTerm n a V η g w y z i) V := by
  have heq : (fun W => ∏ k : Fin n,
      ternaryMass a (g k + η * w k * z) (if k = i then W else V) (y k)) =
      (fun W => ternaryMass a (g i + η * w i * z) W (y i) *
        ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
          ternaryMass a (g k + η * w k * z) V (y k)) := by
    funext W
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [if_neg (Finset.ne_of_mem_erase hk)]
  rw [heq]
  exact (ternary_hasDerivAt_variance a (g i + η * w i * z) V (y i)).mul_const _

private theorem patch_variance_term_eq_product (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) (i : Fin n) :
    patchVarianceTerm n a V η g w y z i =
      ∏ k : Fin n, if k = i then ternaryVarianceDerivative a (y k)
        else ternaryMass a (g k + η * w k * z) V (y k) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  unfold patchVarianceTerm
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [if_neg (Finset.ne_of_mem_erase hk)]

/-- A variance derivative has zero total mass, observation by observation. -/
theorem patch_variance_term_sum_zero (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (z : ℝ) (i : Fin n) :
    ∑ y : Fin n → Fin 3, patchVarianceTerm n a V η g w y z i = 0 := by
  simp_rw [patch_variance_term_eq_product]
  rw [← Fintype.prod_sum (fun k (yk : Fin 3) =>
    if k = i then ternaryVarianceDerivative a yk
      else ternaryMass a (g k + η * w k * z) V yk)]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Fin.sum_univ_succ, ternaryVarianceDerivative]
  ring

/-- The full numerator is centered over the conditional response law. -/
theorem patch_score_numerator_sum_zero (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (z : ℝ) (ha : a ≠ 0) :
    ∑ y : Fin n → Fin 3, patchScoreNumerator n a V η g w y z = 0 := by
  have hD : ∑ y : Fin n → Fin 3,
      symmetricDifference (patchResponseProduct n a V η g w y) = 0 := by
    unfold symmetricDifference
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    rw [patch_response_normalized n a V η g w 1 ha,
      patch_response_normalized n a V η g w (-1) ha,
      patch_response_normalized n a V η g w 0 ha]
    norm_num
  unfold patchScoreNumerator
  rw [Finset.sum_sub_distrib, hD, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, patch_variance_term_sum_zero]
  simp

/-- Conditional response centering of the observable score. -/
theorem patch_observable_score_centered (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (z : ℝ) (ha : a ≠ 0)
    (hpositive : ∀ y : Fin n → Fin 3, 0 < patchResponseProduct n a V η g w y z) :
    ∑ y : Fin n → Fin 3,
      patchResponseProduct n a V η g w y z * patchObservableScore n a V η g w y z = 0 := by
  have heq : ∀ y : Fin n → Fin 3,
      patchResponseProduct n a V η g w y z * patchObservableScore n a V η g w y z =
      patchScoreNumerator n a V η g w y z := by
    intro y
    unfold patchObservableScore
    field_simp [ne_of_gt (hpositive y)]
  simp_rw [heq]
  exact patch_score_numerator_sum_zero n a V η g w z ha

/-- Positivity of the full conditional likelihood follows from positivity
of every observation's response masses. -/
theorem patch_response_positive (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ) (z : ℝ)
    (hpositive : ∀ i y, 0 < ternaryMass a (g i + η * w i * z) V y) :
    ∀ y : Fin n → Fin 3, 0 < patchResponseProduct n a V η g w y z := by
  intro y
  exact Finset.prod_pos (fun i _ => hpositive i (y i))

/-- A finite conditional experiment, with regression depending on the latent
activation vector. The design points can be absorbed into `f`. -/
def finiteResponseLikelihood (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  ∏ i, ternaryMass a (f ξ i) V (y i)

/-- The partial variance derivative of its `i`th observation. -/
def finiteResponseVarianceTerm (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3)
    (y : Fin n → Fin 3) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) *
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (f ξ k) V (y k)

/-- The full variance derivative is the sum of the observation derivatives. -/
theorem finite_response_variance_hasDerivAt (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    HasDerivAt (fun W => finiteResponseLikelihood m n a W f ξ y)
      (∑ i, finiteResponseVarianceTerm m n a V f ξ y i) V := by
  have h := HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => ternary_hasDerivAt_variance a (f ξ i) V (y i))
  simpa [finiteResponseLikelihood, finiteResponseVarianceTerm, smul_eq_mul,
    mul_comm] using h

/-- The observation expectation along the path `V(t)=v-eta^2*t`. -/
def finiteExperimentExpectation (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ *
    ∑ y, finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y * T y

/-- The unnormalized observable derivative for the full finite experiment. -/
def finiteExperimentScoreNumerator (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  (∑ j, latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ) -
    η ^ 2 * ∑ i, finiteResponseVarianceTerm m n a V f ξ y i

/-- The score uses only the data likelihood denominator, never a prior denominator. -/
def finiteExperimentScore (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) : ℝ :=
  finiteExperimentScoreNumerator m n a V η f ξ y /
    finiteResponseLikelihood m n a V f ξ y

private theorem latent_difference_response_sum (m n : ℕ) (j : Fin m)
    (F : (Fin m → Fin 3) → (Fin n → Fin 3) → ℝ) (T : (Fin n → Fin 3) → ℝ)
    (ξ : Fin m → Fin 3) :
    latentDifference m j (fun ξ' => ∑ y, F ξ' y * T y) ξ =
      ∑ y, latentDifference m j (fun ξ' => F ξ' y) ξ * T y := by
  simp [latentDifference, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- Exact observable score representation of the derivative of every data
observable in the finite latent/response experiment. -/
theorem finite_experiment_observable_score_hasDerivAt (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ)
    (hpositive : ∀ ξ y, 0 < finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y) :
    HasDerivAt (fun u => finiteExperimentExpectation m n a v η u f T)
      (∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
        ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y *
          T y * finiteExperimentScore m n a (v - η ^ 2 * t) η f ξ y) t := by
  let V := v - η ^ 2 * t
  let L : (Fin m → Fin 3) → (Fin n → Fin 3) → ℝ :=
    finiteResponseLikelihood m n a V f
  let U : (Fin m → Fin 3) → (Fin n → Fin 3) → ℝ :=
    fun ξ y => ∑ i, finiteResponseVarianceTerm m n a V f ξ y i
  have hV : HasDerivAt (fun u : ℝ => v - η ^ 2 * u) (-η ^ 2) t :=
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2))).congr_deriv (by ring)
  have hF : ∀ ξ : Fin m → Fin 3,
      HasDerivAt (fun u => ∑ y : Fin n → Fin 3,
        finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y * T y)
        (-η ^ 2 * ∑ y : Fin n → Fin 3, U ξ y * T y) t := by
    intro ξ
    have hy : ∀ y : Fin n → Fin 3,
        HasDerivAt (fun u => finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y * T y)
          ((-η ^ 2 * U ξ y) * T y) t := by
      intro y
      have hcomp : HasDerivAt
          (fun u => finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y)
          (-η ^ 2 * U ξ y) t :=
        (by
          have hcomp0 := (finite_response_variance_hasDerivAt m n a
            (v - η ^ 2 * t) f ξ y).comp t hV
          exact hcomp0.congr_deriv (by dsimp [U, V]; ring))
      exact hcomp.mul_const (T y)
    convert HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → Fin 3)))
      (fun y _ => hy y) using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have h := activation_expectation_hasDerivAt m t
    (fun u ξ => ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y * T y)
    (fun ξ => -η ^ 2 * ∑ y : Fin n → Fin 3, U ξ y * T y) hF
  change HasDerivAt _ _ t at h
  apply h.congr_deriv
  have hprior := activation_prior_derivative_replacement m t
    (fun ξ => ∑ y : Fin n → Fin 3, L ξ y * T y)
  have hscore : ∀ ξ y,
      L ξ y * T y * finiteExperimentScore m n a V η f ξ y =
        ((∑ j, latentDifference m j (fun ξ' => L ξ' y) ξ) - η ^ 2 * U ξ y) * T y := by
    intro ξ y
    dsimp [L, U, finiteExperimentScore, finiteExperimentScoreNumerator]
    have hL : finiteResponseLikelihood m n a V f ξ y ≠ 0 := ne_of_gt (hpositive ξ y)
    field_simp [hL]
  change (∑ ξ : Fin m → Fin 3,
      (activationProductPriorDerivative m t ξ * (∑ y, L ξ y * T y) +
        activationProductPrior m t ξ * (-η ^ 2 * ∑ y, U ξ y * T y))) =
      ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
        ∑ y : Fin n → Fin 3, L ξ y * T y * finiteExperimentScore m n a V η f ξ y
  rw [Finset.sum_add_distrib, hprior]
  have hDsum (ξ : Fin m → Fin 3) :
      (∑ j, latentDifference m j (fun ξ' => ∑ y, L ξ' y * T y) ξ) =
        ∑ y, (∑ j, latentDifference m j (fun ξ' => L ξ' y) ξ) * T y := by
    simp_rw [latent_difference_response_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_mul]
  simp_rw [hDsum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ _
  simp_rw [hscore]
  rw [← mul_add]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Every conditional response distribution of the full experiment normalizes. -/
theorem finite_response_normalized (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (ha : a ≠ 0) :
    ∑ y, finiteResponseLikelihood m n a V f ξ y = 1 := by
  unfold finiteResponseLikelihood
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

/-- The conditional response derivative in any observation has zero total mass. -/
theorem finite_response_variance_term_sum_zero (m n : ℕ) (a V : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (i : Fin n) :
    ∑ y, finiteResponseVarianceTerm m n a V f ξ y i = 0 := by
  simpa [patchVarianceTerm, finiteResponseVarianceTerm] using
    patch_variance_term_sum_zero n a V 0 (f ξ) (fun _ => 0) 0 i

/-- The experiment's unnormalized score is centered conditionally on the latent state. -/
theorem finite_experiment_score_numerator_centered (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (ha : a ≠ 0) :
    ∑ y, finiteExperimentScoreNumerator m n a V η f ξ y = 0 := by
  have hD (j : Fin m) :
      ∑ y : Fin n → Fin 3,
        latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ = 0 := by
    unfold latentDifference
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    simp [finite_response_normalized m n a V f _ ha]
    ring
  unfold finiteExperimentScoreNumerator
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  conv_lhs => lhs; rw [Finset.sum_comm]
  conv_lhs => rhs; arg 2; rw [Finset.sum_comm]
  simp [hD, finite_response_variance_term_sum_zero]

/-- Actual conditional centering of the experiment's score. -/
theorem finite_experiment_score_centered (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ξ : Fin m → Fin 3) (ha : a ≠ 0)
    (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) :
    ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood m n a V f ξ y * finiteExperimentScore m n a V η f ξ y = 0 := by
  have heq (y : Fin n → Fin 3) :
      finiteResponseLikelihood m n a V f ξ y * finiteExperimentScore m n a V η f ξ y =
        finiteExperimentScoreNumerator m n a V η f ξ y := by
    unfold finiteExperimentScore
    field_simp [ne_of_gt (hpositive y)]
  simp_rw [heq]
  exact finite_experiment_score_numerator_centered m n a V η f ξ ha

/-- The finite-design version of the random regression field. -/
def latentRegression (m n : ℕ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (i : Fin n) : ℝ :=
  base i + η * ∑ j, w i j * ternaryValue 1 (ξ j)

/-- Regression with coordinate `j` excluded from the field. -/
def latentRegressionWithout (m n : ℕ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (j : Fin m) (i : Fin n) : ℝ :=
  base i + η * ∑ k ∈ (Finset.univ : Finset (Fin m)).erase j, w i k * ternaryValue 1 (ξ k)

/-- Replacing a latent coordinate changes the field only through its own window. -/
theorem latent_regression_update (m n : ℕ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (j : Fin m) (i : Fin n) (z : Fin 3) :
    latentRegression m n η base w (Function.update ξ j z) i =
      latentRegressionWithout m n η base w ξ j i + η * w i j * ternaryValue 1 z := by
  unfold latentRegression latentRegressionWithout
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  have heq : (∑ k ∈ (Finset.univ : Finset (Fin m)).erase j,
      w i k * ternaryValue 1 (Function.update ξ j z k)) =
      ∑ k ∈ (Finset.univ : Finset (Fin m)).erase j, w i k * ternaryValue 1 (ξ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [heq]
  ring

/-- The current field has the same excluded-coordinate decomposition. -/
theorem latent_regression_decomposition (m n : ℕ) (η : ℝ) (base : Fin n → ℝ)
    (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3) (j : Fin m) (i : Fin n) :
    latentRegression m n η base w ξ i =
      latentRegressionWithout m n η base w ξ j i + η * w i j * ternaryValue 1 (ξ j) := by
  simpa using latent_regression_update m n η base w ξ j i (ξ j)

/-- The actual coordinate likelihood replacement equals the one-dimensional
patch finite difference used in the cancellation proof. -/
theorem latent_regression_likelihood_difference (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (y : Fin n → Fin 3) :
    latentDifference m j
      (fun ξ' => finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ' y) ξ =
      symmetricDifference (patchResponseProduct n a V η
        (latentRegressionWithout m n η base w ξ j) (fun i => w i j) y) := by
  simp [latentDifference, finiteResponseLikelihood, symmetricDifference,
    patchResponseProduct, latent_regression_update, ternaryValue]

/-- The observation variance terms also agree under this patch representation. -/
theorem latent_regression_variance_term (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (y : Fin n → Fin 3) (i : Fin n) :
    finiteResponseVarianceTerm m n a V (latentRegression m n η base w) ξ y i =
      patchVarianceTerm n a V η (latentRegressionWithout m n η base w ξ j)
        (fun k => w k j) y (ternaryValue 1 (ξ j)) i := by
  simp [finiteResponseVarianceTerm, patchVarianceTerm, latent_regression_decomposition m n η base w ξ j]

/-- Each coordinate numerator in the actual regression-field experiment has
zero contribution when its support contains at most one observation. -/
theorem latent_regression_singleton_cancel (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (y : Fin n → Fin 3) (ha : a ≠ 0) (i : Fin n)
    (hw : ∀ k, k ≠ i → w k j = 0) :
    latentDifference m j
      (fun ξ' => finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ' y) ξ -
      η ^ 2 * ∑ k, (w k j) ^ 2 *
        finiteResponseVarianceTerm m n a V (latentRegression m n η base w) ξ y k = 0 := by
  rw [latent_regression_likelihood_difference]
  simp_rw [latent_regression_variance_term m n a V η base w ξ j]
  exact patch_score_cancel_singleton n a V η
    (latentRegressionWithout m n η base w ξ j) (fun k => w k j) y
    (ternaryValue 1 (ξ j)) ha i hw

/-- One coordinate's unnormalized observable score in the full finite experiment. -/
def finiteCoordinateScoreNumerator (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) (j : Fin m) : ℝ :=
  latentDifference m j (fun ξ' => finiteResponseLikelihood m n a V f ξ' y) ξ -
    η ^ 2 * ∑ i, (w i j) ^ 2 * finiteResponseVarianceTerm m n a V f ξ y i

/-- One coordinate's observable score, as in equation (small-s-score). -/
def finiteCoordinateScore (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) (j : Fin m) : ℝ :=
  finiteCoordinateScoreNumerator m n a V η f w ξ y j / finiteResponseLikelihood m n a V f ξ y

/-- The sum-of-squares window identity decomposes the full score numerator
into the paper's coordinate numerators. -/
theorem finite_experiment_score_numerator_decomposition (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3)
    (hw : ∀ i, ∑ j, (w i j) ^ 2 = 1) :
    finiteExperimentScoreNumerator m n a V η f ξ y =
      ∑ j, finiteCoordinateScoreNumerator m n a V η f w ξ y j := by
  unfold finiteExperimentScoreNumerator finiteCoordinateScoreNumerator
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, hw]
  simp

/-- The observable full score equals the sum of its coordinate scores. -/
theorem finite_experiment_score_decomposition (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3)
    (hw : ∀ i, ∑ j, (w i j) ^ 2 = 1) :
    finiteExperimentScore m n a V η f ξ y =
      ∑ j, finiteCoordinateScore m n a V η f w ξ y j := by
  unfold finiteExperimentScore finiteCoordinateScore
  rw [finite_experiment_score_numerator_decomposition m n a V η f w ξ y hw,
    Finset.sum_div]

/-- A coordinate score is centered over responses for every fixed latent state. -/
theorem finite_coordinate_score_numerator_centered (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (j : Fin m) (ha : a ≠ 0) :
    ∑ y, finiteCoordinateScoreNumerator m n a V η f w ξ y j = 0 := by
  unfold finiteCoordinateScoreNumerator latentDifference
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, finite_response_variance_term_sum_zero]
  simp [finite_response_normalized m n a V f _ ha]
  ring

theorem finite_coordinate_score_centered (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (j : Fin m) (ha : a ≠ 0)
    (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) :
    ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood m n a V f ξ y * finiteCoordinateScore m n a V η f w ξ y j = 0 := by
  have heq (y : Fin n → Fin 3) :
      finiteResponseLikelihood m n a V f ξ y * finiteCoordinateScore m n a V η f w ξ y j =
        finiteCoordinateScoreNumerator m n a V η f w ξ y j := by
    unfold finiteCoordinateScore
    field_simp [ne_of_gt (hpositive y)]
  simp_rw [heq]
  exact finite_coordinate_score_numerator_centered m n a V η f w ξ j ha

/-- Zero-observation cancellation in the actual regression-field model. -/
theorem latent_regression_zero_cancel (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (y : Fin n → Fin 3) (hw : ∀ i, w i j = 0) :
    finiteCoordinateScoreNumerator m n a V η (latentRegression m n η base w) w ξ y j = 0 := by
  unfold finiteCoordinateScoreNumerator
  rw [latent_regression_likelihood_difference]
  simp_rw [latent_regression_variance_term m n a V η base w ξ j]
  exact patch_score_cancel_zero n a V η
    (latentRegressionWithout m n η base w ξ j) (fun k => w k j) y
    (ternaryValue 1 (ξ j)) hw

/-- The coordinate score itself vanishes for support count at most one. -/
theorem latent_regression_singleton_score_zero (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (y : Fin n → Fin 3) (ha : a ≠ 0) (i : Fin n)
    (hw : ∀ k, k ≠ i → w k j = 0) :
    finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j = 0 := by
  unfold finiteCoordinateScore finiteCoordinateScoreNumerator
  rw [latent_regression_singleton_cancel m n a V η base w ξ j y ha i hw]
  simp

/-- The finite latent-response joint law normalizes. -/
theorem finite_experiment_joint_normalized (m n : ℕ) (a V t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ha : a ≠ 0) :
    ∑ ξ : Fin m → Fin 3, ∑ y : Fin n → Fin 3,
      activationProductPrior m t ξ * finiteResponseLikelihood m n a V f ξ y = 1 := by
  simp_rw [← Finset.mul_sum, finite_response_normalized m n a V f _ ha, mul_one]
  exact activation_product_prior_normalized m t

/-- Its masses are nonnegative in the probability range of the activation prior. -/
theorem finite_experiment_joint_nonnegative (m n : ℕ) (a V t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hresponse : ∀ ξ i y, 0 ≤ ternaryMass a (f ξ i) V y) :
    ∀ ξ y, 0 ≤ activationProductPrior m t ξ * finiteResponseLikelihood m n a V f ξ y := by
  intro ξ y
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative t ht ht1 (ξ j))
  · exact Finset.prod_nonneg (fun i _ => hresponse ξ i (y i))

end

end NearlyMinimax
