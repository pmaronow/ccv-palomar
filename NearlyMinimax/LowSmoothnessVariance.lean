module

public import NearlyMinimax.LowSmoothness


@[expose] public section

/-! # Product Taylor estimates and small-count energy

Analytic and counting estimates for the low-smoothness score. Bounds on
individual response probabilities and their derivatives are propagated
through the actual product likelihood; no score-energy bound is assumed.
-/

namespace NearlyMinimax

noncomputable section

/-- First derivative of a finite product, in the product-rule representation. -/
def finiteProductFirst {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d : ι → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ s, (∏ j ∈ s.erase i, q j z) * d i z

/-- Second derivative obtained by differentiating that product rule. -/
def finiteProductSecond {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d e : ι → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ s, ((∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) * d i z +
    (∏ j ∈ s.erase i, q j z) * e i z)

/-- This is the actual first derivative, rather than just a formal expression. -/
theorem finite_product_hasDerivAt {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d : ι → ℝ → ℝ) (z : ℝ) (hq : ∀ i ∈ s, HasDerivAt (q i) (d i z) z) :
    HasDerivAt (fun u => ∏ i ∈ s, q i u) (finiteProductFirst s q d z) z := by
  simpa [finiteProductFirst, smul_eq_mul] using HasDerivAt.fun_finset_prod hq

/-- This is the actual derivative of the first product derivative. -/
theorem finite_product_first_hasDerivAt {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d e : ι → ℝ → ℝ) (z : ℝ)
    (hq : ∀ i ∈ s, HasDerivAt (q i) (d i z) z)
    (hd : ∀ i ∈ s, HasDerivAt (d i) (e i z) z) :
    HasDerivAt (finiteProductFirst s q d) (finiteProductSecond s q d e z) z := by
  unfold finiteProductFirst finiteProductSecond
  apply HasDerivAt.fun_sum
  intro i hi
  have hrest : HasDerivAt (fun u => ∏ j ∈ s.erase i, q j u)
      (∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) z := by
    simpa [smul_eq_mul] using HasDerivAt.fun_finset_prod
      (fun j hj => hq j (Finset.mem_of_mem_erase hj))
  exact hrest.mul (hd i hi)

private theorem abs_finite_product_le_one {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, |q i| ≤ 1) : |∏ i ∈ s, q i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg (q i)) hq

/-- Product derivative bound, including the dependence on the number of factors. -/
theorem finite_product_first_abs_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d : ι → ℝ → ℝ) (z B : ℝ) (_hB : 0 ≤ B)
    (hq : ∀ i ∈ s, |q i z| ≤ 1) (hd : ∀ i ∈ s, |d i z| ≤ B) :
    |finiteProductFirst s q d z| ≤ s.card * B := by
  unfold finiteProductFirst
  calc
    _ ≤ ∑ i ∈ s, |(∏ j ∈ s.erase i, q j z) * d i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hp : |∏ j ∈ s.erase i, q j z| ≤ 1 :=
        abs_finite_product_le_one _ _ (fun j hj => hq j (Finset.mem_of_mem_erase hj))
      calc
        _ ≤ 1 * B := mul_le_mul hp (hd i hi) (abs_nonneg _) (by norm_num)
        _ = B := one_mul B
    _ = _ := by simp

/-- A second product derivative has at most a quadratic factor-count cost. -/
theorem finite_product_second_abs_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q d e : ι → ℝ → ℝ) (z B1 B2 : ℝ) (hB1 : 0 ≤ B1) (_hB2 : 0 ≤ B2)
    (hq : ∀ i ∈ s, |q i z| ≤ 1) (hd : ∀ i ∈ s, |d i z| ≤ B1)
    (he : ∀ i ∈ s, |e i z| ≤ B2) :
    |finiteProductSecond s q d e z| ≤ s.card * (s.card * B1 ^ 2 + B2) := by
  unfold finiteProductSecond
  calc
    _ ≤ ∑ i ∈ s, |(∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) * d i z +
        (∏ j ∈ s.erase i, q j z) * e i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ((s.card : ℝ) * B1 ^ 2 + B2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hfirst := finite_product_first_abs_bound (s.erase i) q d z B1 hB1
        (fun j hj => hq j (Finset.mem_of_mem_erase hj))
        (fun j hj => hd j (Finset.mem_of_mem_erase hj))
      have hcard : ((s.erase i).card : ℝ) ≤ s.card := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset i s)
      have hfirst' : |∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z| ≤ s.card * B1 :=
        hfirst.trans (mul_le_mul_of_nonneg_right hcard hB1)
      have hp : |∏ j ∈ s.erase i, q j z| ≤ 1 :=
        abs_finite_product_le_one _ _ (fun j hj => hq j (Finset.mem_of_mem_erase hj))
      calc
        _ ≤ |(∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, q k z) * d j z) * d i z| +
            |(∏ j ∈ s.erase i, q j z) * e i z| := abs_add_le _ _
        _ ≤ (s.card * B1) * B1 + 1 * B2 := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul hfirst' (hd i hi) (abs_nonneg _) (by positivity))
            (mul_le_mul hp (he i hi) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    _ = _ := by simp; ring

/-- A symmetric second difference is controlled by the second derivative
on `[-1,1]`. This is a mean-value proof of the Taylor remainder estimate. -/
theorem symmetric_difference_abs_bound (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |E z| ≤ B) :
    |symmetricDifference H| ≤ B := by
  have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hDdiff (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : |D z - D 0| ≤ B := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hD x hx).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hE x hx)
      (convex_Icc (-1 : ℝ) 1) hzero hz
    simp only [Real.norm_eq_abs, sub_zero] at h
    have hzabs : |z| ≤ 1 := abs_le.mpr hz
    exact h.trans (by nlinarith)
  let G : ℝ → ℝ := fun z => H z - H 0 - z * D 0
  have hG (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
      HasDerivAt G (D z - D 0) z := by
    exact (((hH z hz).sub_const (H 0)).sub
      ((hasDerivAt_id z).mul_const (D 0))).congr_deriv (by ring)
  have hGbound (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : |G z| ≤ B * |z| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hG x hx).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hDdiff x hx)
      (convex_Icc (-1 : ℝ) 1) hzero hz
    simpa [G, Real.norm_eq_abs] using h
  have hp : |H 1 - H 0 - D 0| ≤ B := by
    simpa [G] using hGbound 1 (by norm_num)
  have hm : |H (-1) - H 0 + D 0| ≤ B := by
    simpa [G] using hGbound (-1) (by norm_num)
  have heq : symmetricDifference H =
      (1 / 2 : ℝ) * (H 1 - H 0 - D 0) + (1 / 2 : ℝ) * (H (-1) - H 0 + D 0) := by
    unfold symmetricDifference
    ring
  rw [heq]
  calc
    _ ≤ |(1 / 2 : ℝ) * (H 1 - H 0 - D 0)| +
        |(1 / 2 : ℝ) * (H (-1) - H 0 + D 0)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * B + (1 / 2 : ℝ) * B := by
      rw [abs_mul, abs_mul]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_le_mul_of_nonneg_left hm (by norm_num))
    _ = B := by ring

/-- A finite product's symmetric difference inherits its derivative bounds. -/
theorem finite_product_symmetric_difference_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q d e : ι → ℝ → ℝ) (B1 B2 : ℝ)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hq : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, HasDerivAt (q i) (d i z) z)
    (hd : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, HasDerivAt (d i) (e i z) z)
    (h0 : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, |q i z| ≤ 1)
    (h1 : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, |d i z| ≤ B1)
    (h2 : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i ∈ s, |e i z| ≤ B2) :
    |symmetricDifference (fun z => ∏ i ∈ s, q i z)| ≤
      s.card * (s.card * B1 ^ 2 + B2) := by
  apply symmetric_difference_abs_bound _ (finiteProductFirst s q d)
    (finiteProductSecond s q d e)
  · positivity
  · intro z hz
    exact finite_product_hasDerivAt s q d z (hq z hz)
  · intro z hz
    exact finite_product_first_hasDerivAt s q d e z (hq z hz) (hd z hz)
  · intro z hz
    exact finite_product_second_abs_bound s q d e z B1 B2 hB1 hB2
      (h0 z hz) (h1 z hz) (h2 z hz)

/-- Actual first latent-direction derivative of an observation's response mass. -/
def patchFactorFirst (n : ℕ) (a _V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (z : ℝ) : ℝ :=
  (η * w i) * ternaryMeanDerivative a (g i + η * w i * z) (y i)

/-- Actual second latent-direction derivative of that response mass. -/
def patchFactorSecond (n : ℕ) (a η : ℝ) (w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (_z : ℝ) : ℝ :=
  (η * w i) ^ 2 * ternaryMeanSecondDerivative a (y i)

theorem patch_factor_hasDerivAt (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (z : ℝ) :
    HasDerivAt (fun u => ternaryMass a (g i + η * w i * u) V (y i))
      (patchFactorFirst n a V η g w y i z) z := by
  have hx : HasDerivAt (fun u : ℝ => g i + η * w i * u) (η * w i) z := by
    simpa using ((hasDerivAt_id z).const_mul (η * w i)).const_add (g i)
  have h := (ternary_hasDerivAt_mean a (g i + η * w i * z) V (y i)).comp z hx
  exact h.congr_deriv (by unfold patchFactorFirst; ring)

theorem patch_factor_first_hasDerivAt (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) (z : ℝ) :
    HasDerivAt (patchFactorFirst n a V η g w y i)
      (patchFactorSecond n a η w y i z) z := by
  have hx : HasDerivAt (fun u : ℝ => g i + η * w i * u) (η * w i) z := by
    simpa using ((hasDerivAt_id z).const_mul (η * w i)).const_add (g i)
  have h := ((ternary_hasDerivAt_mean_derivative a (g i + η * w i * z) (y i)).comp z hx).const_mul (η * w i)
  exact h.congr_deriv (by unfold patchFactorSecond; ring)

/-- The quadratic-in-count Taylor bound for the actual response product. -/
theorem patch_product_symmetric_difference_bound (n : ℕ) (a V η M N : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMass a (g i + η * w i * z) V (y i)| ≤ 1)
    (hfirst : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMeanDerivative a (g i + η * w i * z) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N) :
    |symmetricDifference (patchResponseProduct n a V η g w y)| ≤
      ((n : ℝ) ^ 2 * M ^ 2 + n * N) * η ^ 2 := by
  have hd : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |patchFactorFirst n a V η g w y i z| ≤ |η| * M := by
    intro z hz i
    unfold patchFactorFirst
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (|η| * 1) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg η))
          (hfirst z hz i) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |patchFactorSecond n a η w y i z| ≤ η ^ 2 * N := by
    intro z _ i
    unfold patchFactorSecond
    rw [abs_mul, abs_pow, abs_mul, mul_pow, sq_abs]
    have hwi : |w i| ^ 2 ≤ 1 := by nlinarith [hw i, abs_nonneg (w i)]
    calc
      _ ≤ (η ^ 2 * 1) * N :=
        mul_le_mul (mul_le_mul_of_nonneg_left hwi (sq_nonneg η))
          (hsecond i) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h := finite_product_symmetric_difference_bound
    (Finset.univ : Finset (Fin n))
    (fun i z => ternaryMass a (g i + η * w i * z) V (y i))
    (patchFactorFirst n a V η g w y) (patchFactorSecond n a η w y)
    (|η| * M) (η ^ 2 * N) (by positivity) (by positivity)
    (fun z _ i _ => patch_factor_hasDerivAt n a V η g w y i z)
    (fun z _ i _ => patch_factor_first_hasDerivAt n a V η g w y i z)
    (fun z hz i _ => hq z hz i) (fun z hz i _ => hd z hz i) (fun z hz i _ => he z hz i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  convert h using 1
  · rfl
  · rw [mul_pow, sq_abs]
    ring

/-- The variance correction grows at most linearly in the patch count. -/
theorem patch_variance_correction_abs_bound (n : ℕ) (a V η z B : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hB : 0 ≤ B) (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ i, |ternaryMass a (g i + η * w i * z) V (y i)| ≤ 1)
    (hvariance : ∀ i, |ternaryVarianceDerivative a (y i)| ≤ B) :
    |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| ≤ n * B := by
  calc
    _ ≤ ∑ i : Fin n, |(w i) ^ 2 * patchVarianceTerm n a V η g w y z i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, B := by
      apply Finset.sum_le_sum
      intro i _
      unfold patchVarianceTerm
      rw [abs_mul, abs_pow, abs_mul]
      have hwi : |w i| ^ 2 ≤ 1 := by nlinarith [hw i, abs_nonneg (w i)]
      have hprod : |∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
          ternaryMass a (g k + η * w k * z) V (y k)| ≤ 1 :=
        abs_finite_product_le_one _ _ (fun k _ => hq k)
      calc
        _ ≤ 1 * (B * 1) := mul_le_mul hwi
          (mul_le_mul (hvariance i) hprod (abs_nonneg _) hB)
          (by positivity) (by norm_num)
        _ = B := by ring
    _ = _ := by simp

/-- The actual score numerator has the paper's `k^2*eta^2` bound, with
constants determined by individual response derivative bounds. -/
theorem patch_score_numerator_abs_bound (n : ℕ) (a V η z M N B : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hn : 1 ≤ n)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hM : 0 ≤ M) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMass a (g i + η * w i * u) V (y i)| ≤ 1)
    (hfirst : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMeanDerivative a (g i + η * w i * u) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N)
    (hvariance : ∀ i, |ternaryVarianceDerivative a (y i)| ≤ B) :
    |patchScoreNumerator n a V η g w y z| ≤
      (M ^ 2 + N + B) * (n : ℝ) ^ 2 * η ^ 2 := by
  have hD := patch_product_symmetric_difference_bound n a V η M N g w y hM hN
    hw hq hfirst hsecond
  have hV := patch_variance_correction_abs_bound n a V η z B g w y hB hw (hq z hz) hvariance
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hNB : (n : ℝ) * (N + B) ≤ (n : ℝ) ^ 2 * (N + B) :=
    mul_le_mul_of_nonneg_right hnn (by positivity)
  have htriangle : |patchScoreNumerator n a V η g w y z| ≤
      |symmetricDifference (patchResponseProduct n a V η g w y)| +
        η ^ 2 * |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| := by
    unfold patchScoreNumerator
    have h := abs_sub_le (symmetricDifference (patchResponseProduct n a V η g w y)) 0
      (η ^ 2 * ∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i)
    rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_pow, sq_abs] at h
    exact h
  calc
    _ ≤ |symmetricDifference (patchResponseProduct n a V η g w y)| +
        η ^ 2 * |∑ i, (w i) ^ 2 * patchVarianceTerm n a V η g w y z i| := htriangle
    _ ≤ ((n : ℝ) ^ 2 * M ^ 2 + n * N) * η ^ 2 + η ^ 2 * (n * B) :=
      add_le_add hD (mul_le_mul_of_nonneg_left hV (sq_nonneg η))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hNB (sq_nonneg η)]

/-- A uniform positive mass bound propagates to the actual product denominator. -/
theorem patch_response_lower_bound (n : ℕ) (a V η z c : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hc : 0 ≤ c)
    (hq : ∀ i, c ≤ ternaryMass a (g i + η * w i * z) V (y i)) :
    c ^ n ≤ patchResponseProduct n a V η g w y z := by
  calc
    _ = ∏ _i : Fin n, c := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc) (fun i _ => hq i)

/-- Explicit score-square bound for `n` observations in the patch. It displays
both the polynomial count factor and the exponential likelihood denominator. -/
theorem patch_score_square_bound (n : ℕ) (a V η z M N B c : ℝ)
    (g w : Fin n → ℝ) (y : Fin n → Fin 3) (hn : 1 ≤ n)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hM : 0 ≤ M) (hN : 0 ≤ N) (hB : 0 ≤ B) (hc : 0 < c)
    (hw : ∀ i, |w i| ≤ 1)
    (hq : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMass a (g i + η * w i * u) V (y i)| ≤ 1)
    (hfirst : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |ternaryMeanDerivative a (g i + η * w i * u) (y i)| ≤ M)
    (hsecond : ∀ i, |ternaryMeanSecondDerivative a (y i)| ≤ N)
    (hvariance : ∀ i, |ternaryVarianceDerivative a (y i)| ≤ B)
    (hlower : ∀ i, c ≤ ternaryMass a (g i + η * w i * z) V (y i)) :
    (patchObservableScore n a V η g w y z) ^ 2 ≤
      (M ^ 2 + N + B) ^ 2 * (n : ℝ) ^ 4 * η ^ 4 / c ^ (2 * n) := by
  have hnum := patch_score_numerator_abs_bound n a V η z M N B g w y hn hz hM hN hB
    hw hq hfirst hsecond hvariance
  have hden := patch_response_lower_bound n a V η z c g w y hc.le hlower
  have hcp : 0 < c ^ n := pow_pos hc n
  have hL : 0 < patchResponseProduct n a V η g w y z := hcp.trans_le hden
  have hscore : |patchObservableScore n a V η g w y z| ≤
      (M ^ 2 + N + B) * (n : ℝ) ^ 2 * η ^ 2 / c ^ n := by
    unfold patchObservableScore
    rw [abs_div, abs_of_pos hL]
    exact div_le_div₀ (by positivity) hnum hcp hden
  have hs := mul_self_le_mul_self (abs_nonneg _) hscore
  rw [← sq, sq_abs] at hs
  convert hs using 1
  rw [show 2 * n = n * 2 by omega, pow_mul]
  ring

/-- Polynomial count growth can be absorbed into a fixed exponential. -/
theorem fourth_power_count_le_exponential (n : ℕ) : (n : ℝ) ^ 4 ≤ (16 : ℝ) ^ n := by
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4
  calc
    _ ≤ ((2 : ℝ) ^ n) ^ 4 := h
    _ = (16 : ℝ) ^ n := by rw [← pow_mul, Nat.mul_comm n 4, pow_mul]; norm_num

/-- The precise polynomial/denominator score bound implies the `C^k*eta^4`
bound used in the paper, with an explicit constant depending only on `K,c`. -/
theorem score_bound_exponential_absorption (n : ℕ) (K c η r : ℝ) (hn : 1 ≤ n) (hc : 0 < c)
    (hr : r ^ 2 ≤ K ^ 2 * (n : ℝ) ^ 4 * η ^ 4 / c ^ (2 * n)) :
    r ^ 2 ≤ (16 * max 1 (K ^ 2) / c ^ 2) ^ n * η ^ 4 := by
  have hK : K ^ 2 ≤ (max 1 (K ^ 2)) ^ n := by
    exact (le_max_right 1 (K ^ 2)).trans (by
      simpa using pow_le_pow_right₀ (le_max_left 1 (K ^ 2)) hn)
  have hn4 := fourth_power_count_le_exponential n
  have hnum : K ^ 2 * (n : ℝ) ^ 4 * η ^ 4 ≤
      (max 1 (K ^ 2)) ^ n * (16 : ℝ) ^ n * η ^ 4 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hK hn4 (by positivity) (by positivity)) (by positivity)
  calc
    _ ≤ K ^ 2 * (n : ℝ) ^ 4 * η ^ 4 / c ^ (2 * n) := hr
    _ ≤ (max 1 (K ^ 2)) ^ n * (16 : ℝ) ^ n * η ^ 4 / c ^ (2 * n) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [div_pow, mul_pow, ← pow_mul]; ring

/-- Finite exponential-series tail from order two, uniformly in its cutoff. -/
theorem finite_exponential_tail_bound (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), if 2 ≤ k then x ^ k / (k.factorial : ℝ) else 0) ≤
      x ^ 2 * Real.exp x := by
  rw [Nat.add_comm n 2, Finset.sum_range_add]
  have hsmall : (∑ k ∈ Finset.range 2, if 2 ≤ k then x ^ k / (k.factorial : ℝ) else 0) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hsmall, zero_add]
  simp only [show ∀ k : ℕ, 2 ≤ 2 + k by omega, ↓reduceIte]
  calc
    _ ≤ ∑ k ∈ Finset.range n, x ^ 2 * (x ^ k / (k.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _
      have hfac : (k.factorial : ℝ) ≤ ((2 + k).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (show k ≤ 2 + k by omega)
      calc
        _ ≤ x ^ (2 + k) / (k.factorial : ℝ) :=
          div_le_div₀ (by positivity) le_rfl (by positivity) hfac
        _ = _ := by rw [pow_add]; ring
    _ = x ^ 2 * (∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ x ^ 2 * Real.exp x :=
      mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx n) (sq_nonneg x)

/-- The binomial count law, represented by its actual finite masses. -/
def binomialCountMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

theorem binomial_count_mass_normalized (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomialCountMass n p k = 1 := by
  have h := add_pow p (1 - p) n
  have hs : p + (1 - p) = 1 := by ring
  rw [hs, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  unfold binomialCountMass
  ring

theorem binomial_count_mass_nonnegative (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomialCountMass n p k := by
  have h1mp : 0 ≤ 1 - p := by linarith
  unfold binomialCountMass
  positivity

/-- Weighted probability of a count at least two has quadratic small-mean
behavior. This is the count-tail bound used for the low-smoothness energy. -/
theorem binomial_count_tail_energy (n : ℕ) (p C : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hmean : n * p ≤ 1) :
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then binomialCountMass n p k * C ^ k else 0) ≤
      C ^ 2 * Real.exp C * (n * p) ^ 2 := by
  have hx : 0 ≤ C * n * p := by positivity
  have hterm (k : ℕ) : binomialCountMass n p k * C ^ k ≤
      (C * n * p) ^ k / (k.factorial : ℝ) := by
    have hremaining : (1 - p) ^ (n - k) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hchoose := Nat.choose_le_pow_div (α := ℝ) k n
    calc
      _ ≤ ((n.choose k : ℝ) * p ^ k * 1) * C ^ k := by
        unfold binomialCountMass
        gcongr
      _ ≤ (((n : ℝ) ^ k / (k.factorial : ℝ)) * p ^ k * 1) * C ^ k := by gcongr
      _ = _ := by rw [mul_pow, mul_pow]; ring
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), if 2 ≤ k then (C * n * p) ^ k / (k.factorial : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> simp_all only [le_refl]
    _ ≤ ∑ k ∈ Finset.range (n + 2), if 2 ≤ k then (C * n * p) ^ k / (k.factorial : ℝ) else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; positivity)
    _ ≤ (C * n * p) ^ 2 * Real.exp (C * n * p) := finite_exponential_tail_bound _ hx n
    _ ≤ C ^ 2 * Real.exp C * (n * p) ^ 2 := by
      have hexp : Real.exp (C * n * p) ≤ Real.exp C := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hmean hC]
      nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg (C * n * p))]

/-- Uniform regression-direction derivative bound on an admissible bounded field. -/
theorem ternary_mean_derivative_abs_bound (a f ρ : ℝ) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hf : |f| ≤ ρ) (y : Fin 3) :
    |ternaryMeanDerivative a f y| ≤ (2 * ρ + a) / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hA : 0 ≤ 2 * ρ + a := by positivity
  have hm : |2 * f - a| ≤ 2 * ρ + a := by
    have h := abs_sub_le (2 * f) 0 a
    rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos ha] at h
    norm_num at h
    linarith
  have hp : |2 * f + a| ≤ 2 * ρ + a := by
    have h := abs_add_le (2 * f) a
    rw [abs_mul, abs_of_pos ha] at h
    norm_num at h
    linarith
  have hhalf : (2 * ρ + a) / (2 * a ^ 2) ≤ (2 * ρ + a) / a ^ 2 :=
    div_le_div₀ hA le_rfl ha2 (by nlinarith)
  fin_cases y
  · change |(2 * f - a) / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2)]
    exact (div_le_div_of_nonneg_right hm (by positivity)).trans hhalf
  · change |-(2 * f) / a ^ 2| ≤ _
    rw [abs_div, abs_neg, abs_mul, abs_of_pos ha2]
    norm_num
    exact div_le_div_of_nonneg_right (by linarith) ha2.le
  · change |(2 * f + a) / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2)]
    exact (div_le_div_of_nonneg_right hp (by positivity)).trans hhalf

/-- Uniform second derivative bound, independent of the regression value. -/
theorem ternary_mean_second_derivative_abs_bound (a : ℝ) (ha : 0 < a) (y : Fin 3) :
    |ternaryMeanSecondDerivative a y| ≤ 2 / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  fin_cases y
  · change |1 / a ^ 2| ≤ _
    rw [abs_div, abs_of_pos ha2, abs_one]
    exact div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ha2.le
  · change |-2 / a ^ 2| ≤ _
    simp [abs_div, abs_of_pos ha2]
  · change |1 / a ^ 2| ≤ _
    rw [abs_div, abs_of_pos ha2, abs_one]
    exact div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ha2.le

/-- Uniform variance derivative bound. -/
theorem ternary_variance_derivative_abs_bound (a : ℝ) (ha : 0 < a) (y : Fin 3) :
    |ternaryVarianceDerivative a y| ≤ 1 / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  fin_cases y
  · change |1 / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2), abs_one]
    exact div_le_div₀ (show (0 : ℝ) ≤ 1 by norm_num) le_rfl ha2
      (show a ^ 2 ≤ 2 * a ^ 2 by nlinarith)
  · change |-1 / a ^ 2| ≤ _
    simp [abs_div, abs_of_pos ha2]
  · change |1 / (2 * a ^ 2)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * a ^ 2), abs_one]
    exact div_le_div₀ (show (0 : ℝ) ≤ 1 by norm_num) le_rfl ha2
      (show a ^ 2 ≤ 2 * a ^ 2 by nlinarith)

/-- Response-averaged squared observable patch score. -/
def patchExpectedScoreEnergy (n : ℕ) (a V η : ℝ) (g w : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ y : Fin n → Fin 3,
    patchResponseProduct n a V η g w y z * (patchObservableScore n a V η g w y z) ^ 2

/-- An explicit exponential constant for the admissible ternary score bound. -/
def ternaryScoreExponentialConstant (a ρ c : ℝ) : ℝ :=
  16 * max 1 ((((2 * ρ + a) / a ^ 2) ^ 2 + 3 / a ^ 2) ^ 2) / c ^ 2

/-- Actual response score energy is bounded by `C^k*eta^4`, with all
constants deduced from the bounded regression field and legal masses. -/
theorem patch_expected_score_energy_bound (n : ℕ) (a V η z ρ c : ℝ)
    (g w : Fin n → ℝ) (hn : 1 ≤ n) (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hw : ∀ i, |w i| ≤ 1)
    (hreg : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i, |g i + η * w i * u| ≤ ρ)
    (hq : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i y,
      0 ≤ ternaryMass a (g i + η * w i * u) V y ∧ ternaryMass a (g i + η * w i * u) V y ≤ 1)
    (hlower : ∀ i y, c ≤ ternaryMass a (g i + η * w i * z) V y) :
    patchExpectedScoreEnergy n a V η g w z ≤ ternaryScoreExponentialConstant a ρ c ^ n * η ^ 4 := by
  let M := (2 * ρ + a) / a ^ 2
  let K := M ^ 2 + 3 / a ^ 2
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hy (y : Fin n → Fin 3) : (patchObservableScore n a V η g w y z) ^ 2 ≤
      ternaryScoreExponentialConstant a ρ c ^ n * η ^ 4 := by
    have hs := patch_score_square_bound n a V η z M (2 / a ^ 2) (1 / a ^ 2) c g w y hn hz
      (by dsimp [M]; positivity) (by positivity) (by positivity) hc hw
      (fun u hu i => (abs_of_nonneg (hq u hu i (y i)).1).trans_le (hq u hu i (y i)).2)
      (fun u hu i => ternary_mean_derivative_abs_bound a _ ρ ha hρ (hreg u hu i) (y i))
      (fun i => ternary_mean_second_derivative_abs_bound a ha (y i))
      (fun i => ternary_variance_derivative_abs_bound a ha (y i)) (fun i => hlower i (y i))
    have hK : M ^ 2 + 2 / a ^ 2 + 1 / a ^ 2 = K := by dsimp [K]; ring
    rw [hK] at hs
    simpa [ternaryScoreExponentialConstant, K, M] using
      score_bound_exponential_absorption n K c η _ hn hc hs
  unfold patchExpectedScoreEnergy
  calc
    _ ≤ ∑ y : Fin n → Fin 3,
        patchResponseProduct n a V η g w y z * (ternaryScoreExponentialConstant a ρ c ^ n * η ^ 4) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hy y) (le_trans
        (pow_nonneg hc.le n) (patch_response_lower_bound n a V η z c g w y hc.le (fun i => hlower i (y i))))
    _ = _ := by rw [← Finset.sum_mul, patch_response_normalized n a V η g w z (ne_of_gt ha), one_mul]

/-- Exact zero-count energy cancellation. -/
theorem patch_expected_score_energy_zero (a V η z : ℝ) (g w : Fin 0 → ℝ) :
    patchExpectedScoreEnergy 0 a V η g w z = 0 := by
  unfold patchExpectedScoreEnergy
  apply Finset.sum_eq_zero
  intro y _
  have hnum := patch_score_cancel_zero 0 a V η g w y z (fun i => Fin.elim0 i)
  simp [patchObservableScore, hnum]

/-- Exact one-count energy cancellation. -/
theorem patch_expected_score_energy_one (a V η z : ℝ) (g w : Fin 1 → ℝ) (ha : a ≠ 0) :
    patchExpectedScoreEnergy 1 a V η g w z = 0 := by
  unfold patchExpectedScoreEnergy
  apply Finset.sum_eq_zero
  intro y _
  have hw : ∀ k : Fin 1, k ≠ 0 → w k = 0 := by
    intro k h
    exact False.elim (h (Fin.eq_zero k))
  have hnum := patch_score_cancel_singleton 1 a V η g w y z ha 0 hw
  simp [patchObservableScore, hnum]

/-- The binomial count-tail bound integrates any countwise exponential energy
bound that vanishes at counts zero and one. -/
theorem binomial_collision_energy_bound (n : ℕ) (p C η : ℝ) (e : ℕ → ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hmean : n * p ≤ 1)
    (he0 : e 0 = 0) (he1 : e 1 = 0)
    (he : ∀ k, 2 ≤ k → e k ≤ C ^ k * η ^ 4) :
    (∑ k ∈ Finset.range (n + 1), binomialCountMass n p k * e k) ≤
      C ^ 2 * Real.exp C * η ^ 4 * (n * p) ^ 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        if 2 ≤ k then binomialCountMass n p k * (C ^ k * η ^ 4) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : 2 ≤ k
      · rw [if_pos hk]
        exact mul_le_mul_of_nonneg_left (he k hk) (binomial_count_mass_nonnegative n p hp hp1 k)
      · rw [if_neg hk]
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl <;> simp [he0, he1]
    _ = η ^ 4 * (∑ k ∈ Finset.range (n + 1),
        if 2 ≤ k then binomialCountMass n p k * C ^ k else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    _ ≤ η ^ 4 * (C ^ 2 * Real.exp C * (n * p) ^ 2) :=
      mul_le_mul_of_nonneg_left (binomial_count_tail_energy n p C hp hp1 hC hmean) (by positivity)
    _ = _ := by ring

/-- Actual expected score energy under a binomial patch count. The legal
conditional experiments may vary with the count, while their field and
probability bounds are uniform. This gives `O(eta^4*(n*p)^2)` directly. -/
theorem binomial_patch_score_energy_bound (n : ℕ) (a V η z ρ c p : ℝ)
    (g w : (k : ℕ) → Fin k → ℝ)
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c) (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hmean : n * p ≤ 1)
    (hw : ∀ k, 2 ≤ k → ∀ i, |w k i| ≤ 1)
    (hreg : ∀ k, 2 ≤ k → ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |g k i + η * w k i * u| ≤ ρ)
    (hq : ∀ k, 2 ≤ k → ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i y,
      0 ≤ ternaryMass a (g k i + η * w k i * u) V y ∧
        ternaryMass a (g k i + η * w k i * u) V y ≤ 1)
    (hlower : ∀ k, 2 ≤ k → ∀ i y, c ≤ ternaryMass a (g k i + η * w k i * z) V y) :
    (∑ k ∈ Finset.range (n + 1), binomialCountMass n p k *
      patchExpectedScoreEnergy k a V η (g k) (w k) z) ≤
      (ternaryScoreExponentialConstant a ρ c) ^ 2 *
        Real.exp (ternaryScoreExponentialConstant a ρ c) * η ^ 4 * (n * p) ^ 2 := by
  apply binomial_collision_energy_bound n p (ternaryScoreExponentialConstant a ρ c) η
    (fun k => patchExpectedScoreEnergy k a V η (g k) (w k) z) hp hp1
  · unfold ternaryScoreExponentialConstant
    positivity
  · exact hmean
  · exact patch_expected_score_energy_zero a V η z (g 0) (w 0)
  · exact patch_expected_score_energy_one a V η z (g 1) (w 1) (ne_of_gt ha)
  · intro k hk
    exact patch_expected_score_energy_bound k a V η z ρ c (g k) (w k) (by omega)
      ha hρ hc hz (hw k hk) (hreg k hk) (hq k hk) (hlower k hk)

end

end NearlyMinimax
