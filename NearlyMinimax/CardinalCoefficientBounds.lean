module

public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.CardinalSeparatedComposition
public import NearlyMinimax.HighFrameNormProduct


@[expose] public section

/-! Actual coefficient bounds for the division-free spatial cardinal
polynomials, including collisions. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def spatialAffineExponent {d : ℕ} (z : Fin d × Bool) : Fin d →₀ ℕ :=
  if z.2 then 0 else Finsupp.single z.1 1

def spatialAffineCoefficient {d : ℕ} (x y : Covariate d) (z : Fin d × Bool) : ℝ :=
  if z.2 then (y z.1 - x z.1) * y z.1 else -8 * (y z.1 - x z.1)

theorem spatial_cardinal_affine_monomial_sum {d : ℕ} (x y : Covariate d) :
    spatialCardinalAffine x y =
      ∑ z : Fin d × Bool, MvPolynomial.monomial (spatialAffineExponent z) (spatialAffineCoefficient x y z) := by
  classical
  rw [Fintype.sum_prod_type]
  unfold spatialCardinalAffine
  apply Finset.sum_congr rfl
  intro r hr
  rw [Fintype.sum_bool]
  simp only [spatialAffineExponent, spatialAffineCoefficient, Bool.false_eq_true, ite_false, ite_true]
  rw [← MvPolynomial.C_apply, ← MvPolynomial.C_mul_X_eq_monomial]
  rw [show (-8 : ℝ) * (y r - x r) = -(8 * (y r - x r)) by ring, map_neg]
  ring

theorem spatial_cardinal_affine_coefficient_l1_le {d : ℕ} (x y : Covariate d)
    (hy : ∀ r, |y r| ≤ 2) :
    frameCoefficientL1 (spatialCardinalAffine x y) ≤ 10 * ∑ r, |y r - x r| := by
  rw [spatial_cardinal_affine_monomial_sum]
  apply (frameCoefficientL1_sum_monomial_le _ _).trans
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  rw [Fintype.sum_bool]
  simp only [spatialAffineCoefficient, Bool.false_eq_true, ite_false, ite_true, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)]
  have h := mul_le_mul_of_nonneg_left (hy r) (abs_nonneg (y r - x r))
  linarith

/-- The actual affine coefficient norm vanishes at a collision and is
controlled by squared spatial distance everywhere. -/
theorem spatial_cardinal_affine_coefficient_l1_square_le {d : ℕ} (x y : Covariate d)
    (hy : ∀ r, |y r| ≤ 2) :
    (frameCoefficientL1 (spatialCardinalAffine x y)) ^ 2 ≤ 100 * (d : ℝ) * spatialSquaredDistance x y := by
  have hb := spatial_cardinal_affine_coefficient_l1_le x y hy
  have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) (by positivity)).mpr hb
  have hsum := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun r => |y r - x r|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hsum
  change (∑ r, |y r - x r|) ^ 2 ≤ (d : ℝ) * spatialSquaredDistance x y at hsum
  nlinarith

theorem spatial_cardinal_polynomial_coefficient_l1_square_le {d n : ℕ}
    (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2) (i : Fin n) :
    (frameCoefficientL1 (spatialCardinalPolynomial U i)) ^ 2 ≤
      (100 * (d : ℝ)) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) := by
  rw [spatial_cardinal_polynomial_scale_product]
  have hp := frameCoefficientL1_prod Finset.univ (fun j : SpatialScaleIndex i => spatialCardinalAffine (U i) (U j.val))
  have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) (Finset.prod_nonneg (fun _ _ => frameCoefficientL1_nonneg _))).mpr hp
  calc
    _ ≤ (∏ j : SpatialScaleIndex i, frameCoefficientL1 (spatialCardinalAffine (U i) (U j.val))) ^ 2 := hs
    _ = ∏ j : SpatialScaleIndex i, (frameCoefficientL1 (spatialCardinalAffine (U i) (U j.val))) ^ 2 := by rw [Finset.prod_pow]
    _ ≤ ∏ j : SpatialScaleIndex i, 100 * (d : ℝ) * spatialSquaredDistance (U i) (U j.val) :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
        (fun j _ => spatial_cardinal_affine_coefficient_l1_square_le _ _ (hU j.val))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

def spatialMatrixL1 {d D : ℕ} (A : HighFrameIndex d D → HighFrameIndex d D → ℝ) : ℝ :=
  ∑ β, ∑ β', |A β β'|

theorem spatial_matrix_l1_nonnegative {d D : ℕ} (A : HighFrameIndex d D → HighFrameIndex d D → ℝ) :
    0 ≤ spatialMatrixL1 A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem spatial_centered_matrix_l1_eq {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t) =
      |spatialCardinalScale lam (spatialScaleExtend i t) U i| *
        (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) ^ 2 := by
  unfold spatialMatrixL1 spatialCenteredCardinalMatrix
  simp_rw [abs_mul]
  rw [show (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
      |spatialCardinalScale lam (spatialScaleExtend i t) U i| *
        |highFrameCoefficients (spatialCardinalPolynomial U i) β| *
        |highFrameCoefficients (spatialCardinalPolynomial U i) β'|) =
      |spatialCardinalScale lam (spatialScaleExtend i t) U i| *
        (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) *
        (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]]
  ring

theorem spatial_cardinal_scale_nonnegative {d n : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    0 ≤ spatialCardinalScale lam (spatialScaleExtend i t) U i := by
  rw [spatial_cardinal_scale_product]
  exact Finset.prod_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (ht j) (sq_nonneg _)) (Real.exp_pos _).le)

theorem spatial_cardinal_weight_eq_scale_distance_product {d n : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialCardinalWeight lam (spatialScaleExtend i t) U i =
      spatialCardinalScale lam (spatialScaleExtend i t) U i *
        (∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val)) ^ 2 := by
  rw [spatial_cardinal_weight_scale_product, spatial_cardinal_scale_product, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  unfold spatialUnaryWeight
  rw [mul_pow]
  ring

/-- Actual pointwise cardinal matrix envelope. Multiplication by the true
Gamma weight avoids division, so this includes every collision. -/
theorem spatial_centered_matrix_l1_square_le_weight_scale {d n D : ℕ}
    (i : Fin n) (lam : ℝ) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    (spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t)) ^ 2 ≤
      spatialCardinalWeight lam (spatialScaleExtend i t) U i *
        ((100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
          spatialCardinalScale lam (spatialScaleExtend i t) U i) := by
  have hn := spatial_cardinal_scale_nonnegative i lam U t ht
  have hc := (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (frameCoefficientL1_nonneg _)).mpr (highFrameCoefficients_sum_abs_le (D := D) (spatialCardinalPolynomial U i))
  have hb := hc.trans (spatial_cardinal_polynomial_coefficient_l1_square_le U hU i)
  rw [spatial_centered_matrix_l1_eq, abs_of_nonneg hn]
  have hprod : 0 ≤ ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) :=
    Finset.prod_nonneg (fun j _ => Finset.sum_nonneg (fun r _ => sq_nonneg _))
  have hs := (sq_le_sq₀ (mul_nonneg hn (sq_nonneg _)) (mul_nonneg hn (mul_nonneg (by positivity) hprod))).mpr
    (mul_le_mul_of_nonneg_left hb hn)
  apply hs.trans_eq
  rw [spatial_cardinal_weight_eq_scale_distance_product]
  rw [show (100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) =
      ((100 * (d : ℝ)) ^ Fintype.card (SpatialScaleIndex i)) ^ 2 by
    rw [← pow_mul, Nat.mul_comm]]
  ring

end NearlyMinimax
