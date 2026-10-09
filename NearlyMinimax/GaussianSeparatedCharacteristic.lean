module

public import NearlyMinimax.SpatialCardinalCovariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.ComplexMGF


@[expose] public section

/-! Genuine Gaussian characteristic and weighted characteristic identities
for the separated spatial representation in Appendix A. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

abbrev standardGaussianLine : Measure ℝ := gaussianReal 0 1

abbrev standardGaussianPi (d : ℕ) : Measure (Covariate d) :=
  Measure.pi (fun _ => standardGaussianLine)

theorem standardGaussian_complex_exp (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z * x) ∂standardGaussianLine) = Complex.exp (z ^ 2 / 2) := by
  have h := complexMGF_id_gaussianReal (μ := 0) (v := 1) z
  simpa only [complexMGF, id_eq, Complex.ofReal_zero, mul_zero, NNReal.coe_one,
    Complex.ofReal_one, one_mul, zero_add] using h

theorem standardGaussian_complex_exp_hasDerivAt (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (z ^ 2 / 2))
      (z * Complex.exp (z ^ 2 / 2)) z := by
  have hp : HasDerivAt (fun z : ℂ => z ^ 2 / 2) z z := by
    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;>
      simp only [Pi.pow_apply, id_eq] <;> ring
  simpa only [mul_comm] using hp.cexp

theorem standardGaussian_complex_first_moment (z : ℂ) :
    (∫ x : ℝ, (x : ℂ) * Complex.exp (z * x) ∂standardGaussianLine) =
      z * Complex.exp (z ^ 2 / 2) := by
  have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
    simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
  have h := hasDerivAt_complexMGF hz
  have he : complexMGF id standardGaussianLine = fun z => Complex.exp (z ^ 2 / 2) := by
    funext z
    exact standardGaussian_complex_exp z
  rw [he] at h
  exact h.unique (standardGaussian_complex_exp_hasDerivAt z)

theorem standardGaussian_complex_second_moment (z : ℂ) :
    (∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (z * x) ∂standardGaussianLine) =
      (1 + z ^ 2) * Complex.exp (z ^ 2 / 2) := by
  have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
    simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
  have h := hasDerivAt_integral_pow_mul_exp hz 1
  simp only [id_eq, pow_one, Nat.reduceAdd] at h
  have he : (fun z : ℂ => ∫ x : ℝ, (x : ℂ) * Complex.exp (z * x) ∂standardGaussianLine) =
      (fun z => z * Complex.exp (z ^ 2 / 2)) := by
    funext z
    exact standardGaussian_complex_first_moment z
  rw [he] at h
  have hd := (hasDerivAt_id z).mul (standardGaussian_complex_exp_hasDerivAt z)
  have hu := h.unique hd
  exact hu.trans (by simp only [id_eq]; ring)

def gaussianPhase {d : ℕ} (w Z : Covariate d) : ℝ := ∑ l, w l * Z l

theorem standardGaussian_complex_characteristic {d : ℕ} (w : Covariate d) :
    (∫ Z, Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) ∂standardGaussianPi d) =
      Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
  have he : (fun Z : Covariate d => Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) =
      (fun Z => ∏ l, Complex.exp ((w l : ℂ) * Z l * Complex.I)) := by
    funext Z
    simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
      Complex.exp_sum]
  rw [he, integral_fintype_prod_eq_prod (fun (l : Fin d) (x : ℝ) =>
    Complex.exp ((w l : ℂ) * x * Complex.I))]
  have hc (l : Fin d) : (∫ x : ℝ, Complex.exp ((w l : ℂ) * x * Complex.I)
      ∂standardGaussianLine) = Complex.exp ((-(w l) ^ 2 / 2 : ℝ) : ℂ) := by
    rw [← charFun_apply_real, charFun_gaussianReal]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
      one_mul, zero_sub, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    congr 1
    ring
  simp_rw [hc]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_sum, neg_div]
  rw [Finset.sum_neg_distrib, Finset.sum_div]

theorem standardGaussian_cos_characteristic {d : ℕ} (w : Covariate d) :
    (∫ Z, Real.cos (gaussianPhase w Z) ∂standardGaussianPi d) =
      Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
  have hi : Integrable (fun Z : Covariate d =>
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) (standardGaussianPi d) := by
    have hm : Continuous (fun Z : Covariate d => Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) := by
      unfold gaussianPhase
      fun_prop
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun Z => by simp)
  have h := congrArg Complex.re (standardGaussian_complex_characteristic w)
  have hre := integral_re hi
  change (∫ Z, (Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)).re ∂standardGaussianPi d) =
    (∫ Z, Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) ∂standardGaussianPi d).re at hre
  rw [← hre] at h
  simpa only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_re] using h

def gaussianFourierMomentFactor (p : ℕ) (t : ℝ) : ℂ :=
  if p = 0 then 1 else if p = 1 then (t : ℂ) * Complex.I else 1 - (t : ℂ) ^ 2

theorem standardGaussian_line_fourier_moment (p : ℕ) (hp : p ≤ 2) (t : ℝ) :
    (∫ x : ℝ, (x : ℂ) ^ p * Complex.exp ((t : ℂ) * Complex.I * x)
      ∂standardGaussianLine) =
      gaussianFourierMomentFactor p t * Complex.exp ((-t ^ 2 / 2 : ℝ) : ℂ) := by
  have he : ((t : ℂ) * Complex.I) ^ 2 / 2 = ((-t ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
  · simp only [pow_zero, one_mul, gaussianFourierMomentFactor, ite_true]
    rw [standardGaussian_complex_exp, he]
  · simp only [pow_one, gaussianFourierMomentFactor, if_neg (by omega : 1 ≠ 0), ite_true]
    rw [standardGaussian_complex_first_moment, he]
  · simp only [gaussianFourierMomentFactor, if_neg (by omega : 2 ≠ 0), if_neg (by omega : 2 ≠ 1)]
    rw [standardGaussian_complex_second_moment, he]
    congr 1
    rw [mul_pow, Complex.I_sq]
    ring

theorem gaussian_monomial_characteristic_product {d : ℕ} (p : Fin d → ℕ)
    (w Z : Covariate d) :
    (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) =
      ∏ l, (Z l : ℂ) ^ p l * Complex.exp ((w l : ℂ) * Complex.I * Z l) := by
  simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
    Complex.exp_sum, Finset.prod_mul_distrib]
  apply congrArg ((∏ l, (Z l : ℂ) ^ p l) * ·)
  apply Finset.prod_congr rfl
  intro l hl
  congr 1
  ring

theorem gaussian_monomial_characteristic_integrable {d : ℕ} (p : Fin d → ℕ)
    (w : Covariate d) :
    Integrable (fun Z => (∏ l, (Z l : ℂ) ^ p l) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) (standardGaussianPi d) := by
  have hi : ∀ l : Fin d, Integrable (fun x : ℝ => (x : ℂ) ^ p l *
      Complex.exp ((w l : ℂ) * Complex.I * x)) standardGaussianLine := by
    intro l
    have hz : (((w l : ℂ) * Complex.I).re) ∈ interior (integrableExpSet id standardGaussianLine) := by
      simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
    exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz (p l)
  have h := Integrable.fintype_prod (μ := fun _ : Fin d => standardGaussianLine) hi
  convert h using 1
  funext Z
  exact gaussian_monomial_characteristic_product p w Z

theorem standardGaussian_monomial_characteristic {d : ℕ} (p : Fin d → ℕ)
    (hp : ∀ l, p l ≤ 2) (w : Covariate d) :
    (∫ Z, (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)
      ∂standardGaussianPi d) =
      (∏ l, gaussianFourierMomentFactor (p l) (w l)) *
        Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
  simp_rw [gaussian_monomial_characteristic_product]
  rw [integral_fintype_prod_eq_prod (fun (l : Fin d) (x : ℝ) =>
    (x : ℂ) ^ p l * Complex.exp ((w l : ℂ) * Complex.I * x))]
  simp_rw [standardGaussian_line_fourier_moment _ (hp _) _, Finset.prod_mul_distrib]
  apply congrArg ((∏ l, gaussianFourierMomentFactor (p l) (w l)) * ·)
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_sum, neg_div]
  rw [Finset.sum_neg_distrib, Finset.sum_div]

def gaussianCrossExponent {d : ℕ} (a b l : Fin d) : ℕ :=
  (if l = a then 1 else 0) + (if l = b then 1 else 0)

theorem gaussianCrossExponent_le_two {d : ℕ} (a b l : Fin d) :
    gaussianCrossExponent a b l ≤ 2 := by unfold gaussianCrossExponent; split_ifs <;> omega

theorem gaussianCrossExponent_prod {d : ℕ} (a b : Fin d) (Z : Covariate d) :
    (∏ l, (Z l : ℂ) ^ gaussianCrossExponent a b l) = (Z a : ℂ) * Z b := by
  classical
  have he (a : Fin d) : (∏ l, (Z l : ℂ) ^ (if l = a then 1 else 0)) = Z a := by
    have hh (l : Fin d) : (Z l : ℂ) ^ (if l = a then 1 else 0) =
        if l = a then (Z a : ℂ) else 1 := by
      split_ifs with hl
      · rw [hl, pow_one]
      · exact pow_zero _
    simp_rw [hh, Fintype.prod_ite_eq']
  simp only [gaussianCrossExponent, pow_add, Finset.prod_mul_distrib, he]

theorem gaussianCrossExponent_factor_prod {d : ℕ} (a b : Fin d) (w : Covariate d) :
    (∏ l, gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l)) =
      (if a = b then (1 : ℂ) else 0) - (w a : ℂ) * w b := by
  classical
  by_cases hab : a = b
  · subst b
    have he (l : Fin d) : gaussianFourierMomentFactor (gaussianCrossExponent a a l) (w l) =
        if l = a then 1 - (w a : ℂ) ^ 2 else 1 := by
      by_cases hl : l = a <;> simp [gaussianCrossExponent, gaussianFourierMomentFactor, hl]
    simp_rw [he]
    rw [Fintype.prod_ite_eq']
    simp only [ite_true, pow_two]
  · have he (l : Fin d) : gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l) =
        (if l = a then (w a : ℂ) * Complex.I else 1) *
          (if l = b then (w b : ℂ) * Complex.I else 1) := by
      by_cases hla : l = a
      · subst l
        simp [gaussianCrossExponent, gaussianFourierMomentFactor, hab]
      · by_cases hlb : l = b
        · subst l
          simp [gaussianCrossExponent, gaussianFourierMomentFactor, hab, Ne.symm hab]
        · simp [gaussianCrossExponent, gaussianFourierMomentFactor, hla, hlb]
    simp_rw [he, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rw [if_neg hab]
    calc
      _ = (w a : ℂ) * w b * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring

theorem standardGaussian_cross_complex_characteristic {d : ℕ} (w : Covariate d) (a b : Fin d) :
    (∫ Z, ((Z a : ℂ) * Z b) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)
      ∂standardGaussianPi d) =
      ((if a = b then (1 : ℂ) else 0) - (w a : ℂ) * w b) *
        Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
  have h := standardGaussian_monomial_characteristic (gaussianCrossExponent a b)
    (gaussianCrossExponent_le_two a b) w
  simpa only [gaussianCrossExponent_prod, gaussianCrossExponent_factor_prod] using h

theorem gaussian_cross_complex_characteristic_integrable {d : ℕ} (w : Covariate d) (a b : Fin d) :
    Integrable (fun Z => ((Z a : ℂ) * Z b) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) (standardGaussianPi d) := by
  simpa only [gaussianCrossExponent_prod] using
    gaussian_monomial_characteristic_integrable (gaussianCrossExponent a b) w

theorem gaussian_hermite_complex_characteristic_integrable {d : ℕ} (w : Covariate d) (a b : Fin d) :
    Integrable (fun Z => ((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) (standardGaussianPi d) := by
  have hi := gaussian_monomial_characteristic_integrable (fun _ : Fin d => 0) w
  simp only [pow_zero, Finset.prod_const_one, one_mul] at hi
  have h := (hi.const_mul (if a = b then (1 : ℂ) else 0)).sub
    (gaussian_cross_complex_characteristic_integrable w a b)
  convert h using 1
  funext Z
  exact sub_mul _ _ _

theorem standardGaussian_hermite_complex_characteristic {d : ℕ} (w : Covariate d) (a b : Fin d) :
    (∫ Z, ((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) ∂standardGaussianPi d) =
      ((w a : ℂ) * w b) * Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
  have hi := gaussian_monomial_characteristic_integrable (fun _ : Fin d => 0) w
  simp only [pow_zero, Finset.prod_const_one, one_mul] at hi
  simp_rw [sub_mul]
  rw [integral_sub (hi.const_mul _) (gaussian_cross_complex_characteristic_integrable w a b),
    integral_const_mul, standardGaussian_complex_characteristic,
    standardGaussian_cross_complex_characteristic]
  ring

/-- The genuine Gaussian second characteristic moment needed in the paper's
bounded separated affine-kernel representation. -/
theorem standardGaussian_hermite_cos_characteristic {d : ℕ} (w : Covariate d) (a b : Fin d) :
    (∫ Z, ((if a = b then (1 : ℝ) else 0) - Z a * Z b) *
      Real.cos (gaussianPhase w Z) ∂standardGaussianPi d) =
      (w a * w b) * Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
  have hi := gaussian_hermite_complex_characteristic_integrable w a b
  have h := congrArg Complex.re (standardGaussian_hermite_complex_characteristic w a b)
  have hre := integral_re hi
  change (∫ Z, (((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
    Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)).re ∂standardGaussianPi d) =
      (∫ Z, ((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
        Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) ∂standardGaussianPi d).re at hre
  rw [← hre] at h
  simpa only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, add_zero, zero_add,
    mul_zero, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_re,
    apply_ite Complex.re, Complex.one_re, Complex.zero_re, apply_ite Complex.im,
    Complex.one_im, Complex.zero_im, ite_self] using h

end NearlyMinimax
