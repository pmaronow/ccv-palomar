module

public import NearlyMinimax.GaussianMonomialProducts


@[expose] public section

/-! Genuine product Gaussian mark amplitudes: measurability, integrability,
and exponential coefficient cost, with no prescribed tensor budget. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

instance gaussianPrimitiveMeasure_isFinite (d : ℕ) : IsFiniteMeasure (gaussianPrimitiveMeasure d) :=
  gaussianPrimitiveMeasure_finite d

def gaussianPrimitiveScalar (d : ℕ) (lam : ℝ) (e : GaussianPrimitiveMark d) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1

theorem gaussianPrimitiveScalar_measurable (d : ℕ) (lam : ℝ) :
    Measurable (gaussianPrimitiveScalar d lam) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun Z : Covariate d => lam / 2 * gaussianHermite h.1.1 h.1.2 Z)
  have hm : Measurable (fun Z : Covariate d => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  exact hm.const_mul _

theorem gaussianPrimitiveScalar_slice_integrable (d : ℕ) (lam : ℝ) (h : GaussianPrimitiveIndex d) :
    Integrable (fun Z => gaussianPrimitiveScalar d lam (Z, h)) (standardGaussianPi d) := by
  change Integrable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z) _
  exact (gaussianHermite_integrable h.1.1 h.1.2).const_mul _

theorem gaussianPrimitiveScalar_integrable (d : ℕ) (lam : ℝ) :
    Integrable (gaussianPrimitiveScalar d lam) (gaussianPrimitiveMeasure d) :=
  joint_finite_integrable _ _
    (fun h => (gaussianPrimitiveScalar_measurable d lam).comp (measurable_id.prodMk measurable_const))
    (gaussianPrimitiveScalar_slice_integrable d lam)

theorem gaussianPrimitiveScalar_abs_integral (d : ℕ) (lam : ℝ) :
    (∫ e, |gaussianPrimitiveScalar d lam e| ∂gaussianPrimitiveMeasure d) ≤
      8 * |lam| * (d : ℝ) ^ 2 := by
  have hs (h : GaussianPrimitiveIndex d) :
      (∫ Z, |gaussianPrimitiveScalar d lam (Z, h)| ∂standardGaussianPi d) ≤ |lam| := by
    change (∫ Z, |lam / 2 * gaussianHermite h.1.1 h.1.2 Z| ∂standardGaussianPi d) ≤ |lam|
    simp only [abs_mul, integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left (standardGaussian_hermite_abs_integral_le_two h.1.1 h.1.2)
      (abs_nonneg (lam / 2))
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hm ⊢
    exact hm.trans_eq (by ring)
  rw [gaussianPrimitiveMeasure, integral_prod_symm _ (gaussianPrimitiveScalar_integrable d lam).abs,
    integral_count]
  have hm := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs h)
  convert hm using 1 <;> simp [GaussianPrimitiveIndex, Fintype.card_prod, pow_two] <;> ring

abbrev GaussianTensorMark (κ : Type*) (d : ℕ) := κ → GaussianPrimitiveMark d

def gaussianTensorMeasure (κ : Type*) [Fintype κ] (d : ℕ) : Measure (GaussianTensorMark κ d) :=
  Measure.pi (fun _ => gaussianPrimitiveMeasure d)

def gaussianTensorScalar {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveScalar d lam (e i)

def gaussianTensorLeftPolynomial {κ : Type*} [Fintype κ] {d : ℕ} (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.1) (fun i => (e i).2.2.1.1)

def gaussianTensorRightPolynomial {κ : Type*} [Fintype κ] {d : ℕ} (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.2) (fun i => (e i).2.2.1.2)

def gaussianTensorFrameAmplitude {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : HighFrameIndex d D) : ℝ :=
  gaussianTensorScalar lam e * highFrameCoefficients (gaussianTensorLeftPolynomial e) β *
    highFrameCoefficients (gaussianTensorRightPolynomial e) β'

theorem gaussianTensorMeasure_finite (κ : Type*) [Fintype κ] (d : ℕ) :
    IsFiniteMeasure (gaussianTensorMeasure κ d) := by
  letI : IsFiniteMeasure (gaussianPrimitiveMeasure d) := gaussianPrimitiveMeasure_finite d
  unfold gaussianTensorMeasure
  infer_instance

theorem gaussianTensorMark_standardBorel (κ : Type*) [Fintype κ] (d : ℕ) :
    StandardBorelSpace (GaussianTensorMark κ d) := by infer_instance

theorem gaussianTensorScalar_measurable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) :
    Measurable (gaussianTensorScalar (κ := κ) (d := d) lam) :=
  Finset.measurable_fun_prod _ (fun i _ =>
    (gaussianPrimitiveScalar_measurable d lam).comp (measurable_pi_apply i))

theorem gaussianTensorScalar_integrable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) :
    Integrable (gaussianTensorScalar (κ := κ) (d := d) lam) (gaussianTensorMeasure κ d) :=
  Integrable.fintype_prod (fun _ : κ => gaussianPrimitiveScalar_integrable d lam)

theorem gaussianTensorScalar_abs_integral {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) :
    (∫ e, |gaussianTensorScalar (κ := κ) (d := d) lam e| ∂gaussianTensorMeasure κ d) ≤
      (8 * |lam| * (d : ℝ) ^ 2) ^ Fintype.card κ := by
  unfold gaussianTensorScalar gaussianTensorMeasure
  simp only [Finset.abs_prod]
  rw [integral_fintype_prod_eq_prod (fun (_ : κ) e => |gaussianPrimitiveScalar d lam e|)]
  calc
    _ ≤ ∏ _i : κ, (8 * |lam| * (d : ℝ) ^ 2) := Finset.prod_le_prod₀
      (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
      (fun _ _ => gaussianPrimitiveScalar_abs_integral d lam)
    _ = _ := by simp

theorem gaussianTensorPolynomial_coeff_measurable {κ : Type*} [Fintype κ] {d : ℕ}
    (a : GaussianPrimitiveIndex d → Fin d) (s : GaussianPrimitiveIndex d → Bool) (β : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianTensorMark κ d =>
      (gaussianPolynomialProduct (fun i => a (e i).2) (fun i => s (e i).2)).coeff β) := by
  have hf : Measurable (fun h : κ → GaussianPrimitiveIndex d =>
      (gaussianPolynomialProduct (fun i => a (h i)) (fun i => s (h i))).coeff β) := measurable_of_countable _
  have hg : Measurable (fun e : GaussianTensorMark κ d => fun i => (e i).2) :=
    measurable_pi_iff.mpr (fun i => measurable_snd.comp (measurable_pi_apply i))
  exact hf.comp hg

theorem gaussianTensorFrameAmplitude_measurable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorFrameAmplitude lam e β β') := by
  have hl := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.1) (fun h => h.2.1.1) (polynomialBoxExponent β.val)
  have hr := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.2) (fun h => h.2.1.2) (polynomialBoxExponent β'.val)
  exact ((gaussianTensorScalar_measurable lam).mul hl).mul hr

theorem gaussianTensorFrameAmplitude_cost_bound {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) :
    separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam) e ≤
      |gaussianTensorScalar lam e| * (8 : ℝ) ^ (2 * Fintype.card κ) := by
  have h := gaussianPolynomialProduct_rankone_cost (D := D)
    (fun i : κ => (e i).2.1.1) (fun i => (e i).2.2.1.1)
    (fun i : κ => (e i).2.1.2) (fun i => (e i).2.2.1.2) (gaussianTensorScalar lam e)
  simpa only [two_mul, separatedMatrixCost, gaussianTensorFrameAmplitude,
    gaussianTensorLeftPolynomial, gaussianTensorRightPolynomial] using h

theorem gaussianTensorFrameAmplitude_cost_measurable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ) :
    Measurable (separatedMatrixCost (gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam)) := by
  exact Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
    (fun β' _ => (gaussianTensorFrameAmplitude_measurable lam β β').abs))

theorem gaussianTensorFrameAmplitude_cost_integrable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ) :
    Integrable (separatedMatrixCost (gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam))
      (gaussianTensorMeasure κ d) := by
  apply ((gaussianTensorScalar_integrable (κ := κ) (d := d) lam).abs.mul_const
    ((8 : ℝ) ^ (2 * Fintype.card κ))).mono'
    (gaussianTensorFrameAmplitude_cost_measurable lam).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
    (fun β _ => Finset.sum_nonneg (fun β' _ => abs_nonneg _)))]
  exact gaussianTensorFrameAmplitude_cost_bound lam e

theorem gaussianTensorFrameAmplitude_integrated_cost {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ) :
    (∫ e, separatedMatrixCost (gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam) e
      ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * (d : ℝ) ^ 2) ^ Fintype.card κ := by
  have hm := integral_mono (gaussianTensorFrameAmplitude_cost_integrable (κ := κ) (d := d) (D := D) lam)
    ((gaussianTensorScalar_integrable (κ := κ) (d := d) lam).abs.mul_const ((8 : ℝ) ^ (2 * Fintype.card κ)))
    (gaussianTensorFrameAmplitude_cost_bound lam)
  rw [integral_mul_const] at hm
  have h := mul_le_mul_of_nonneg_right (gaussianTensorScalar_abs_integral (κ := κ) (d := d) lam)
    (by positivity : 0 ≤ (8 : ℝ) ^ (2 * Fintype.card κ))
  apply hm.trans
  apply h.trans_eq
  rw [pow_mul, ← mul_pow]
  congr 1
  ring

def gaussianTensorAmplitude {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : Fin d →₀ ℕ) : ℝ :=
  gaussianTensorScalar lam e * (gaussianTensorLeftPolynomial e).coeff β *
    (gaussianTensorRightPolynomial e).coeff β'

theorem gaussianPolynomialProduct_raw_coefficient_bound {κ : Type*} [Fintype κ] {d : ℕ}
    (a : κ → Fin d) (s : κ → Bool) (β : Fin d →₀ ℕ) :
    |(gaussianPolynomialProduct a s).coeff β| ≤ (8 : ℝ) ^ Fintype.card κ := by
  rw [gaussianPolynomialProduct_monomial]
  simp only [coeff_monomial]
  split_ifs
  · exact gaussianPolynomialProduct_coefficient_bound s
  · simpa only [abs_zero] using (by positivity : (0 : ℝ) ≤ 8 ^ Fintype.card κ)

theorem gaussianTensorAmplitude_measurable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (β β' : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorAmplitude lam e β β') := by
  have hl := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.1) (fun h => h.2.1.1) β
  have hr := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.2) (fun h => h.2.1.2) β'
  exact ((gaussianTensorScalar_measurable lam).mul hl).mul hr

theorem gaussianTensorAmplitude_bound {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : Fin d →₀ ℕ) :
    |gaussianTensorAmplitude lam e β β'| ≤ |gaussianTensorScalar lam e| * (8 : ℝ) ^ (2 * Fintype.card κ) := by
  have hl := gaussianPolynomialProduct_raw_coefficient_bound
    (fun i : κ => (e i).2.1.1) (fun i => (e i).2.2.1.1) β
  have hr := gaussianPolynomialProduct_raw_coefficient_bound
    (fun i : κ => (e i).2.1.2) (fun i => (e i).2.2.1.2) β'
  unfold gaussianTensorAmplitude
  rw [abs_mul, abs_mul, mul_assoc, two_mul, pow_add]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact mul_le_mul hl hr (abs_nonneg _) (by positivity)

theorem gaussianTensorAmplitude_integrable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianTensorMark κ d => gaussianTensorAmplitude lam e β β')
      (gaussianTensorMeasure κ d) := by
  apply ((gaussianTensorScalar_integrable (κ := κ) (d := d) lam).abs.mul_const
    ((8 : ℝ) ^ (2 * Fintype.card κ))).mono'
    (gaussianTensorAmplitude_measurable lam β β').aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun e => by
    simpa only [Real.norm_eq_abs] using gaussianTensorAmplitude_bound lam e β β')

def gaussianTensorObservable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) (t : κ → ℝ)
    (x y : κ → Covariate d) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveLeft lam (t i) (e i) (x i) * gaussianPrimitiveRight lam (t i) (e i) (y i)

theorem gaussianTensorObservable_measurable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (t : κ → ℝ) (x y : κ → Covariate d) :
    Measurable (gaussianTensorObservable lam t x y) := by
  exact Finset.measurable_fun_prod _ (fun i _ =>
    ((gaussianPrimitiveLeft_measurable lam (t i) (x i)).comp (measurable_pi_apply i)).mul
      ((gaussianPrimitiveRight_measurable lam (t i) (y i)).comp (measurable_pi_apply i)))

theorem gaussianTensorObservable_bound {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (t : κ → ℝ) (x y : κ → Covariate d) (hy : ∀ i a, |y i a| ≤ 2) (e : GaussianTensorMark κ d) :
    |gaussianTensorObservable lam t x y e| ≤ 1 := by
  unfold gaussianTensorObservable
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : κ, (1 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => by
      rw [abs_mul]
      exact (mul_le_mul (gaussianPrimitiveLeft_bound lam (t i) (e i) (x i))
        (gaussianPrimitiveRight_bound lam (t i) (e i) (y i) (hy i))
          (abs_nonneg _) (by norm_num)).trans_eq (by ring))
    _ = _ := by simp

/-- The actual tensor observable, on the true product mark measure, has
derived integrability for every coefficient exponent used in convolution. -/
theorem gaussianTensor_observable_integrable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (t : κ → ℝ) (x y : κ → Covariate d) (hy : ∀ i a, |y i a| ≤ 2)
    (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianTensorMark κ d => gaussianTensorAmplitude lam e β β' *
      gaussianTensorObservable lam t x y e) (gaussianTensorMeasure κ d) :=
  (gaussianTensorAmplitude_integrable lam β β').mul_bdd
    (gaussianTensorObservable_measurable lam t x y).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using gaussianTensorObservable_bound lam t x y hy e))

def realMatrixSymmetrize {I : Type*} (A : I → I → ℝ) (i j : I) : ℝ := (A i j + A j i) / 2

theorem realMatrixSymmetrize_symmetric {I : Type*} (A : I → I → ℝ) (i j : I) :
    realMatrixSymmetrize A i j = realMatrixSymmetrize A j i := by
  unfold realMatrixSymmetrize
  ring

theorem separatedMatrixCost_symmetrize_le {E I : Type*} [Fintype I] [DecidableEq I]
    (A : E → I → I → ℝ) (e : E) :
    separatedMatrixCost (fun e => realMatrixSymmetrize (A e)) e ≤ separatedMatrixCost A e := by
  have hp (i j : I) : |realMatrixSymmetrize (A e) i j| ≤ (|A e i j| + |A e j i|) / 2 := by
    unfold realMatrixSymmetrize
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  calc
    _ ≤ ∑ i : I, ∑ j : I, (|A e i j| + |A e j i|) / 2 := Finset.sum_le_sum
      (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = separatedMatrixCost A e := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : I => |A e j i|)]
      unfold separatedMatrixCost
      ring

def gaussianTensorSymmetricAmplitude {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  realMatrixSymmetrize (gaussianTensorFrameAmplitude lam e)

theorem gaussianTensorSymmetricAmplitude_symmetric {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : HighFrameIndex d D) :
    gaussianTensorSymmetricAmplitude lam e β β' = gaussianTensorSymmetricAmplitude lam e β' β :=
  realMatrixSymmetrize_symmetric _ _ _

theorem gaussianTensorSymmetricAmplitude_measurable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorSymmetricAmplitude lam e β β') :=
  ((gaussianTensorFrameAmplitude_measurable lam β β').add
    (gaussianTensorFrameAmplitude_measurable lam β' β)).div_const 2

theorem gaussianTensorSymmetricAmplitude_cost_integrable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ) :
    Integrable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam))
      (gaussianTensorMeasure κ d) := by
  have hm : Measurable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam)) :=
    Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (gaussianTensorSymmetricAmplitude_measurable lam β β').abs))
  apply (gaussianTensorFrameAmplitude_cost_integrable (κ := κ) (d := d) (D := D) lam).mono'
    hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
    (fun β _ => Finset.sum_nonneg (fun β' _ => abs_nonneg _)))]
  exact separatedMatrixCost_symmetrize_le _ e

theorem gaussianTensorSymmetricAmplitude_integrated_cost {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ) :
    (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam) e
      ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * (d : ℝ) ^ 2) ^ Fintype.card κ :=
  (integral_mono (gaussianTensorSymmetricAmplitude_cost_integrable lam)
    (gaussianTensorFrameAmplitude_cost_integrable lam)
    (separatedMatrixCost_symmetrize_le _)).trans (gaussianTensorFrameAmplitude_integrated_cost lam)

end NearlyMinimax
