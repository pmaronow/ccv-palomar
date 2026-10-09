module

public import NearlyMinimax.AnchoredFitError
public import NearlyMinimax.DyadicPilotPopulation


@[expose] public section

/-! Genuine original-law local polynomial fits and their Taylor approximation. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

def dyadicRegressionDifference {d : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ :=
  fun w => θ.regression (dyadicCellAffine j x w) - θ.regression x

/-- The actual local fit, formed from original-law response and density means. -/
def dyadicPopulationFit {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  (dyadicPopulationGram θ j x)⁻¹ *ᵥ
    (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)

theorem dyadicCellAffine_continuous {d : ℕ} (j : ℕ) (x : Covariate d) :
    Continuous (dyadicCellAffine j x) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

theorem dyadicCellAffine_mem_cube {d : ℕ} (j : ℕ) (x w : Covariate d)
    (hw : w ∈ unitCube d) : dyadicCellAffine j x w ∈ unitCube d := by
  apply gridClosedBox_subset_cube ((2 : ℕ) ^ j) (by positivity) (regularGridCell _ (by positivity) x)
  change w ∈ gridAffine _ _ ⁻¹' gridClosedBox _ _
  rwa [gridAffine_preimage_box _ (by positivity) _]

theorem dyadicCellAffine_anchor {d : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j x) = x := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hk : (((2 : ℕ) ^ j : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem dyadicCellAffine_difference {d : ℕ} (j : ℕ) (x w : Covariate d) :
    dyadicCellAffine j x w - x = ((2 : ℝ) ^ j)⁻¹ • (w - dyadicNormalizedAnchor j x) := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  have hk : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

theorem dyadicCellAffine_radius {d : ℕ} (j : ℕ) (x w : Covariate d)
    (hx : x ∈ unitCube d) (hw : w ∈ unitCube d) (i : Fin d) :
    |dyadicCellAffine j x w i - x i| ≤ ((2 : ℝ) ^ j)⁻¹ := by
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d :=
    gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx
  have hi : |w i - dyadicNormalizedAnchor j x i| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩
  have he := congrFun (dyadicCellAffine_difference j x w) i
  change dyadicCellAffine j x w i - x i = ((2 : ℝ) ^ j)⁻¹ *
    (w i - dyadicNormalizedAnchor j x i) at he
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ j)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (mul_one _)

theorem admissible_regression_continuousOn_cube {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ContinuousOn θ.regression (unitCube d) := by
  obtain ⟨F, hF, hreg, hNorm⟩ := hθ.2.2.2.2.1
  exact (hreg.continuousOn.mono C.cube_subset).congr (fun x hx => (hF x hx).symm)

theorem dyadicRegressionDifference_continuousOn {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    ContinuousOn (dyadicRegressionDifference θ j x) (unitCube d) := by
  exact ((admissible_regression_continuousOn_cube C θ hθ).comp
    (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)).sub continuousOn_const

theorem dyadicPopulationFit_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicPopulationFit (ℓ := ℓ) θ j x = anchoredPopulationFit (dyadicNormalizedAnchor j x)
      (dyadicNormalizedDensity θ j x) (dyadicRegressionDifference θ j x) := by
  unfold dyadicPopulationFit anchoredPopulationFit
  rw [dyadicPopulationGram_eq_normalized C θ hθ,
    dyadicResponseMoment_eq_normalized C θ hθ, dyadicConstantMoment_eq_normalized C θ hθ]
  congr 1
  have hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper := (dyadicNormalizedDensity_bounds C θ hθ j x).mono
    (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩)
  have hc : ContinuousOn (θ.regression ∘ dyadicCellAffine j x) (unitCube d) :=
    (admissible_regression_continuousOn_cube C θ hθ).comp
      (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)
  rw [show dyadicRegressionDifference θ j x =
    (θ.regression ∘ dyadicCellAffine j x) - (fun _ => θ.regression x) by rfl,
    anchoredVectorMoment_sub _ _ _ _ (dyadicNormalizedDensity_measurable C θ hθ j x)
      C.densityUpper hp hc continuousOn_const]
  congr 1
  ext γ
  change θ.regression x * (∫ w, dyadicNormalizedDensity θ j x w *
    anchoredFeature (dyadicNormalizedAnchor j x) w γ * 1 ∂cubeVolume d) =
      ∫ w, dyadicNormalizedDensity θ j x w *
        anchoredFeature (dyadicNormalizedAnchor j x) w γ * θ.regression x ∂cubeVolume d
  rw [integral_mul_const]
  simp only [mul_one]
  rw [integral_mul_const]
  ring

/-- The original model supplies a genuine centered polynomial residual on
the normalized cell. Neither coefficients nor approximation are assumed. -/
theorem admissible_dyadic_centered_taylor {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    ∃ c : AnchoredIndex d C.order → ℝ, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w - anchoredFitPolynomial (dyadicNormalizedAnchor j x) c w| ≤
        taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨P, hP, herr⟩ := admissible_regression_taylor C θ hθ x hx
  have hxP : eval x P = θ.regression x := by
    have h := herr x hx
    simp [euclideanNorm, Real.zero_rpow C.smoothness_pos.ne'] at h
    exact (sub_eq_zero.mp h).symm
  let a := regularGridCorner ((2 : ℕ) ^ j) (regularGridCell _ (by positivity) x)
  let h : ℝ := ((2 : ℝ) ^ j)⁻¹
  let Q := affinePullbackPolynomial C.order a h P - MvPolynomial.C (θ.regression x)
  have hQ : Q.totalDegree ≤ C.order := by
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (affinePullbackPolynomial_degree a h P hP) (by simp))
  have hQeval (w : Covariate d) : eval w Q = eval (dyadicCellAffine j x w) P - θ.regression x := by
    simp only [Q, map_sub, eval_C, affinePullbackPolynomial_eval a h P hP]
    have he : (fun i => a i + h * w i) = dyadicCellAffine j x w := by
      funext i
      simp [a, h, dyadicCellAffine, gridAffine]
    rw [he]
  have hQzero : eval (dyadicNormalizedAnchor j x) Q = 0 := by
    rw [hQeval, dyadicCellAffine_anchor, hxP, sub_self]
  obtain ⟨c, hc⟩ := polynomial_centered_representation (dyadicNormalizedAnchor j x) Q hQ hQzero
  refine ⟨c, ?_⟩
  intro w hw
  have heq : dyadicRegressionDifference θ j x w - anchoredFitPolynomial (dyadicNormalizedAnchor j x) c w =
      θ.regression (dyadicCellAffine j x w) - eval (dyadicCellAffine j x w) P := by
    rw [show anchoredFitPolynomial (dyadicNormalizedAnchor j x) c w = eval w Q from (hc w).symm, hQeval]
    unfold dyadicRegressionDifference
    ring
  rw [heq]
  have hy := dyadicCellAffine_mem_cube j x w hw
  have hdist := euclideanNorm_le_coordinate_radius (dyadicCellAffine j x w - x) h
    (by dsimp [h]; positivity) (dyadicCellAffine_radius j x w hx hw)
  have hpow := Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hdist C.smoothness_pos.le
  have hcoef : 0 ≤ (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial :=
    div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _)
      (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  calc
    _ ≤ ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
        euclideanNorm (dyadicCellAffine j x w - x) ^ C.smoothness := herr _ hy
    _ ≤ ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
        (Real.sqrt (d : ℝ) * h) ^ C.smoothness := mul_le_mul_of_nonneg_left hpow hcoef
    _ = _ := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) (by dsimp [h]; positivity)]
      unfold taylorErrorFactor
      ring

/-- Uniform original-model approximation of the actual population fit.
The only nonempty-feature restriction is the positive-order branch. -/
theorem admissible_dyadicPopulationFit_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicPopulationFit (ℓ := C.order) θ j x) w| ≤
        E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hpoint⟩ := anchoredPopulationFit_pointwise_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let E := max 1 ((1 + D * Real.sqrt (d : ℝ)) * (taylorErrorFactor C * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ j x hx w hw
  obtain ⟨c, hc⟩ := admissible_dyadic_centered_taylor C θ hθ j x hx
  let R := taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
      (Real.rpow_nonneg (by positivity) _)
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) x hx
  have hf := hpoint _ hu _ _ (dyadicNormalizedDensity_measurable C θ hθ j x)
    (dyadicNormalizedDensity_bounds C θ hθ j x) (dyadicRegressionDifference_continuousOn C θ hθ j x)
    c R hR hc w hw
  rw [dyadicPopulationFit_eq_normalized C θ hθ]
  apply hf.trans
  have hrad : euclideanNorm (w - dyadicNormalizedAnchor j x) ≤ Real.sqrt (d : ℝ) := by
    have := euclideanNorm_le_coordinate_radius (w - dyadicNormalizedAnchor j x) 1 (by norm_num)
      (fun i => by
        change |w i - dyadicNormalizedAnchor j x i| ≤ 1
        exact abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩)
    simpa only [mul_one] using this
  calc
    _ ≤ R + D * R * Real.sqrt (d : ℝ) := add_le_add (hc w hw)
      (mul_le_mul_of_nonneg_left hrad (mul_nonneg hD.le hR))
    _ = ((1 + D * Real.sqrt (d : ℝ)) * (taylorErrorFactor C * C.holderBound)) *
        (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by dsimp [R]; ring
    _ ≤ E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

end NearlyMinimax
