module

public import NearlyMinimax.CardinalScaleWeights


@[expose] public section

/-! Actual Gaussian spatial domination for the cardinal scale kernels. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem radial_gaussian_factorization {d : ℕ} (b : ℝ) (x y : Covariate d) :
    Real.exp (-b * spatialSquaredDistance x y) =
      ∏ r, Real.exp (-b * (y r - x r) ^ 2) := by
  unfold spatialSquaredDistance
  rw [Finset.mul_sum, Real.exp_sum]

theorem radial_gaussian_integrable {d : ℕ} (b : ℝ) (hb : 0 < b) (x : Covariate d) :
    Integrable (fun y => Real.exp (-b * spatialSquaredDistance x y)) volume := by
  simp_rw [radial_gaussian_factorization]
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (r : Fin d) (y : ℝ) => Real.exp (-b * (y - x r) ^ 2))
    (μ := fun _ : Fin d => (volume : Measure ℝ))
    (fun r => (integrable_exp_neg_mul_sq hb).comp_sub_right (x r))

/-- Exact finite-dimensional Gaussian normalization, including arbitrary
spatial center. -/
theorem radial_gaussian_integral {d : ℕ} (b : ℝ) (x : Covariate d) :
    (∫ y, Real.exp (-b * spatialSquaredDistance x y)) = (Real.sqrt (Real.pi / b)) ^ d := by
  simp_rw [radial_gaussian_factorization]
  rw [integral_fintype_prod_volume_eq_prod
    (fun (r : Fin d) (y : ℝ) => Real.exp (-b * (y - x r) ^ 2))]
  simp_rw [integral_sub_right_eq_self (μ := volume) (fun y : ℝ => Real.exp (-b * y ^ 2)), integral_gaussian]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A second-order exponential-series term absorbs the squared radial
factor at every nonnegative argument. -/
theorem quadratic_exp_absorption (z : ℝ) (hz : 0 ≤ z) :
    z ^ 2 * Real.exp (-2 * z) ≤ 2 * Real.exp (-z) := by
  have h := Real.pow_div_factorial_le_exp z hz 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at h
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-2 * z))
  rw [← Real.exp_add, show z + -2 * z = -z by ring] at hmul
  linarith

/-- The actual unary scale density has the spatial decay factor
(1+t)^-1 before Gaussian integration. -/
theorem unary_scale_density_gaussian_domination (alpha t : ℝ)
    (ha : 0 ≤ alpha) (haHalf : alpha ≤ 1 / 2) (ht : 0 ≤ t) :
    unaryScaleDensity alpha t ≤
      (8 * Real.exp (1 / 2) / (1 + t)) * Real.exp (-((1 + t) * alpha / 2)) := by
  have hs : 0 < 1 + t := by linarith
  let z := (1 + t) * alpha / 2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hAbs := quadratic_exp_absorption z hz
  have he : Real.exp (-(alpha * t)) = Real.exp alpha * Real.exp (-((1 + t) * alpha)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hez : -2 * z = -((1 + t) * alpha) := by dsimp [z]; ring
  rw [hez] at hAbs
  have hαexp : Real.exp alpha ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr haHalf
  have hscaled := mul_le_mul_of_nonneg_left hAbs (by positivity : 0 ≤ 4 / (1 + t) ^ 2)
  have hmain : alpha ^ 2 * Real.exp (-((1 + t) * alpha)) ≤
      8 / (1 + t) ^ 2 * Real.exp (-z) := by
    have hleft : 4 / (1 + t) ^ 2 * (z ^ 2 * Real.exp (-((1 + t) * alpha))) =
        alpha ^ 2 * Real.exp (-((1 + t) * alpha)) := by
      dsimp [z]
      field_simp
      ring
    rw [hleft] at hscaled
    apply hscaled.trans_eq
    ring
  unfold unaryScaleDensity
  rw [he]
  have hp : 0 ≤ t * alpha ^ 2 := by positivity
  calc
    _ = t * Real.exp alpha * (alpha ^ 2 * Real.exp (-((1 + t) * alpha))) := by ring
    _ ≤ t * Real.exp (1 / 2) * (8 / (1 + t) ^ 2 * Real.exp (-z)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hαexp ht) hmain (by positivity) (by positivity)
    _ ≤ (8 * Real.exp (1 / 2) / (1 + t)) * Real.exp (-z) := by
      have hratio : t / (1 + t) ^ 2 ≤ 1 / (1 + t) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hs) hs).mpr
        nlinarith
      have h := mul_le_mul_of_nonneg_right hratio
        (by positivity : 0 ≤ 8 * Real.exp (1 / 2) * Real.exp (-z))
      convert h using 1 <;> ring
    _ = _ := rfl

def spatialPatchBox (d : ℕ) : Set (Covariate d) := Icc (fun _ => -1) (fun _ => 1)

def spatialInterpolationLambda (d : ℕ) : ℝ := 1 / (8 * (d : ℝ))

theorem spatial_patch_alpha_bounds {d : ℕ} (hd : 0 < d) (x y : Covariate d)
    (hx : x ∈ spatialPatchBox d) (hy : y ∈ spatialPatchBox d) :
    0 ≤ spatialInterpolationLambda d * spatialSquaredDistance x y ∧
      spatialInterpolationLambda d * spatialSquaredDistance x y ≤ 1 / 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdist : 0 ≤ spatialSquaredDistance x y := Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have hdistUpper : spatialSquaredDistance x y ≤ 4 * d := by
    unfold spatialSquaredDistance
    calc
      _ ≤ ∑ _r : Fin d, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        have hxr : |x r| ≤ 1 := abs_le.mpr ⟨hx.1 r, hx.2 r⟩
        have hyr : |y r| ≤ 1 := abs_le.mpr ⟨hy.1 r, hy.2 r⟩
        have hsub : |y r - x r| ≤ 2 := (abs_sub _ _).trans (by linarith)
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hsub 2
        simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq
      _ = _ := by simp [mul_comm]
  constructor
  · unfold spatialInterpolationLambda
    positivity
  · unfold spatialInterpolationLambda
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 8 * (d : ℝ))]
    linarith

theorem spatial_unary_patch_integrable {d : ℕ} (lam t : ℝ) (x : Covariate d) :
    IntegrableOn (fun y => spatialUnaryWeight lam t x y) (spatialPatchBox d) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

/-- The paper's unary spatial integral bound, before rewriting the
Gaussian normalization as its (1+t)^(-d/2) power. -/
theorem spatial_unary_patch_integral_bound {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    (∫ y in spatialPatchBox d, spatialUnaryWeight (spatialInterpolationLambda d) t x y) ≤
      (8 * Real.exp (1 / 2) / (1 + t)) *
        (Real.sqrt (Real.pi / (spatialInterpolationLambda d * (1 + t) / 2))) ^ d := by
  let lam := spatialInterpolationLambda d
  let b := lam * (1 + t) / 2
  let A := 8 * Real.exp (1 / 2) / (1 + t)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hInt := (radial_gaussian_integrable b hb x).const_mul A
  have hbound (y : Covariate d) (hy : y ∈ spatialPatchBox d) :
      spatialUnaryWeight lam t x y ≤ A * Real.exp (-b * spatialSquaredDistance x y) := by
    obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd x y hx hy
    have h := unary_scale_density_gaussian_domination (lam * spatialSquaredDistance x y) t ha haHalf ht
    have he : spatialUnaryWeight lam t x y = unaryScaleDensity (lam * spatialSquaredDistance x y) t := by
      unfold spatialUnaryWeight unaryScaleDensity
      rw [show -(t * lam * spatialSquaredDistance x y) = -(lam * spatialSquaredDistance x y * t) by ring]
    rw [← he, show -((1 + t) * (lam * spatialSquaredDistance x y) / 2) =
      -b * spatialSquaredDistance x y by dsimp [b]; ring] at h
    exact h
  calc
    _ ≤ ∫ y in spatialPatchBox d, A * Real.exp (-b * spatialSquaredDistance x y) :=
      setIntegral_mono_on (spatial_unary_patch_integrable lam t x) hInt.integrableOn
        measurableSet_Icc hbound
    _ ≤ ∫ y, A * Real.exp (-b * spatialSquaredDistance x y) :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun y => by positivity)) hInt
    _ = _ := by rw [integral_const_mul, radial_gaussian_integral]

theorem radial_gaussian_scale_normalization (d : ℕ) (lam t : ℝ)
    (hlam : 0 < lam) (ht : 0 ≤ t) :
    (Real.sqrt (Real.pi / (lam * (1 + t) / 2))) ^ d =
      (Real.sqrt (2 * Real.pi / lam)) ^ d * (1 + t) ^ (-(d : ℝ) / 2) := by
  have hs : 0 < 1 + t := by linarith
  have harg : Real.pi / (lam * (1 + t) / 2) = (2 * Real.pi / lam) / (1 + t) := by
    field_simp
  rw [harg, Real.sqrt_div (by positivity), div_pow]
  have hden : (Real.sqrt (1 + t)) ^ d = (1 + t) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + t) ^ (1 / 2 : ℝ)) d,
      ← Real.rpow_mul hs.le]
    congr 1
    ring
  rw [hden, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le, div_eq_mul_inv]

def spatialUnaryIntegralConstant (d : ℕ) : ℝ :=
  8 * Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d

/-- Exact power-form unary spatial decay in Appendix A, proved from
actual Gaussian normalization and exponential-series domination. -/
theorem spatial_unary_patch_integral_decay {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    (∫ y in spatialPatchBox d, spatialUnaryWeight (spatialInterpolationLambda d) t x y) ≤
      spatialUnaryIntegralConstant d * (1 + t) ^ (-(d : ℝ) / 2 - 1) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlam : 0 < spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hs : 0 < 1 + t := by linarith
  apply (spatial_unary_patch_integral_bound hd t ht x hx).trans_eq
  rw [radial_gaussian_scale_normalization d _ _ hlam ht]
  unfold spatialUnaryIntegralConstant
  rw [Real.rpow_sub hs, Real.rpow_one]
  ring

/-- The other unary spatial estimate used in the L² covariance bound. -/
theorem spatial_scale_exponential_patch_integral_decay {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    (∫ y in spatialPatchBox d,
      t * Real.exp (-(t * spatialInterpolationLambda d * spatialSquaredDistance x y))) ≤
      (Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d) *
        (1 + t) ^ (1 - (d : ℝ) / 2) := by
  let lam := spatialInterpolationLambda d
  let b := lam * (1 + t) / 2
  let A := t * Real.exp (1 / 2)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hs : 0 < 1 + t := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hInt := (radial_gaussian_integrable b hb x).const_mul A
  have hActual : IntegrableOn (fun y => t * Real.exp (-(t * lam * spatialSquaredDistance x y)))
      (spatialPatchBox d) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold spatialSquaredDistance
    fun_prop
  have hBound (y : Covariate d) (hy : y ∈ spatialPatchBox d) :
      t * Real.exp (-(t * lam * spatialSquaredDistance x y)) ≤
      A * Real.exp (-b * spatialSquaredDistance x y) := by
    obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd x y hx hy
    have he : -(t * lam * spatialSquaredDistance x y) ≤
        1 / 2 + -b * spatialSquaredDistance x y := by
      dsimp [b]
      nlinarith
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) ht
    rw [Real.exp_add] at h
    exact h.trans_eq (by dsimp [A]; ring)
  calc
    _ ≤ ∫ y in spatialPatchBox d, A * Real.exp (-b * spatialSquaredDistance x y) :=
      setIntegral_mono_on hActual hInt.integrableOn measurableSet_Icc hBound
    _ ≤ ∫ y, A * Real.exp (-b * spatialSquaredDistance x y) :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun y => by dsimp [A]; positivity)) hInt
    _ = A * (Real.sqrt (Real.pi / b)) ^ d := by rw [integral_const_mul, radial_gaussian_integral]
    _ = A * ((Real.sqrt (2 * Real.pi / lam)) ^ d * (1 + t) ^ (-(d : ℝ) / 2)) := by
      rw [radial_gaussian_scale_normalization d lam t hlam ht]
    _ ≤ (Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / lam)) ^ d) *
        (1 + t) ^ (1 - (d : ℝ) / 2) := by
      rw [Real.rpow_sub hs, Real.rpow_one]
      have h := mul_le_mul_of_nonneg_right (show t ≤ 1 + t by linarith)
        (by positivity : 0 ≤ Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / lam)) ^ d /
          (1 + t) ^ ((d : ℝ) / 2))
      dsimp [A]
      rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le]
      convert h using 1 <;> ring

end NearlyMinimax
