module

public import NearlyMinimax.DyadicFit


@[expose] public section

/-! A common actual Taylor polynomial across all dyadic levels. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

def dyadicTaylorCoefficients {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    AnchoredIndex d ℓ → ℝ := (anchoredTransport d ℓ) ^ j *ᵥ c

theorem dyadicTaylorCoefficients_succ {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    dyadicTaylorCoefficients c (j + 1) = anchoredTransport d ℓ *ᵥ dyadicTaylorCoefficients c j := by
  rw [dyadicTaylorCoefficients, pow_succ', ← Matrix.mulVec_mulVec]
  rfl

theorem dyadicTaylorCoefficients_evaluation {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ)
    (j : ℕ) (x z : Covariate d) :
    dyadicAnchoredFeature j x z ⬝ᵥ dyadicTaylorCoefficients c j = anchoredFitPolynomial x c z := by
  induction j with
  | zero =>
    simp only [dyadicTaylorCoefficients, pow_zero, Matrix.one_mulVec, dyadicAnchoredFeature,
      one_mul, anchoredFeature, anchoredFitPolynomial, dotProduct]
    apply Finset.sum_congr rfl
    intro γ _
    rw [show (fun i => z i - x i) = z - x by rfl]
    ring
  | succ j ih =>
    rw [dyadicTaylorCoefficients_succ, dyadicAnchoredFeature_transport_dot, ih]

theorem dyadicTaylorCoefficients_normalized_evaluation {d ℓ : ℕ}
    (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) (x w : Covariate d) :
    anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
      anchoredFitPolynomial x c (dyadicCellAffine j x w) := by
  have he := dyadicTaylorCoefficients_evaluation c j x (dyadicCellAffine j x w)
  have hφ : dyadicAnchoredFeature (ℓ := ℓ) j x (dyadicCellAffine j x w) =
      anchoredFeature (dyadicNormalizedAnchor j x) w := by
    funext γ
    exact dyadicAnchoredFeature_affine j x w γ
  rw [hφ] at he
  calc
    _ = anchoredFeature (dyadicNormalizedAnchor j x) w ⬝ᵥ dyadicTaylorCoefficients c j := by
      unfold anchoredFitPolynomial dotProduct
      apply Finset.sum_congr rfl
      intro γ _
      ring
    _ = _ := he

theorem euclideanNorm_smul {d : ℕ} (a : ℝ) (v : Covariate d) :
    euclideanNorm (a • v) = |a| * euclideanNorm v := by
  unfold euclideanNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem dyadicCellAffine_euclidean_distance {d : ℕ} (j : ℕ) (x w : Covariate d) :
    euclideanNorm (dyadicCellAffine j x w - x) =
      ((2 : ℝ) ^ j)⁻¹ * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
  rw [dyadicCellAffine_difference, euclideanNorm_smul, abs_of_nonneg (by positivity)]

/-- One actual Taylor polynomial generates a coherent coefficient family at
every level and a genuine residual bound, uniformly in the original model. -/
theorem admissible_dyadic_taylor_family {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    ∃ c : AnchoredIndex d C.order → ℝ, ∀ j : ℕ, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness ∧
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
            (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness *
              euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness := by
  obtain ⟨P, hP, herr⟩ := admissible_regression_taylor C θ hθ x hx
  have hxP : eval x P = θ.regression x := by
    have h := herr x hx
    simp [euclideanNorm, Real.zero_rpow C.smoothness_pos.ne'] at h
    exact (sub_eq_zero.mp h).symm
  have hP0 : (P - MvPolynomial.C (θ.regression x)).totalDegree ≤ C.order :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le hP (by simp))
  have hzero : eval x (P - MvPolynomial.C (θ.regression x)) = 0 := by
    rw [map_sub, eval_C, hxP, sub_self]
  obtain ⟨c, hc⟩ := polynomial_centered_representation x _ hP0 hzero
  refine ⟨c, ?_⟩
  intro j w hw
  have heq : dyadicRegressionDifference θ j x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
        θ.regression (dyadicCellAffine j x w) - eval (dyadicCellAffine j x w) P := by
    rw [dyadicTaylorCoefficients_normalized_evaluation,
      show anchoredFitPolynomial x c (dyadicCellAffine j x w) =
        eval (dyadicCellAffine j x w) (P - MvPolynomial.C (θ.regression x)) from (hc _).symm,
      map_sub, eval_C]
    unfold dyadicRegressionDifference
    ring
  rw [heq]
  have hy := dyadicCellAffine_mem_cube j x w hw
  have hcoef : 0 ≤ (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial :=
    div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _)
      (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  constructor
  · have hdist := euclideanNorm_le_coordinate_radius (dyadicCellAffine j x w - x)
      (((2 : ℝ) ^ j)⁻¹) (by positivity) (dyadicCellAffine_radius j x w hx hw)
    have hpow := Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hdist C.smoothness_pos.le
    apply (herr _ hy).trans
    apply (mul_le_mul_of_nonneg_left hpow hcoef).trans_eq
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)]
    unfold taylorErrorFactor
    ring
  · convert herr _ hy using 1
    rw [dyadicCellAffine_euclidean_distance, Real.mul_rpow (by positivity)
      (by unfold euclideanNorm; positivity)]
    ring

end NearlyMinimax
