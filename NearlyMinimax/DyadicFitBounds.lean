module

public import NearlyMinimax.DyadicTaylor


@[expose] public section

/-! The original population increment and spatial approximation bounds in U2. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem bounded_rpow_le_linear (r M s : ℝ) (hr : 0 ≤ r) (hrM : r ≤ M) (hs : 1 ≤ s) :
    r ^ s ≤ max 1 (M ^ s) * r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_self_of_le_one hr hr1 hs).trans
      (by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 (M ^ s)) hr)
  · have h1r : 1 ≤ r := (le_of_not_ge hr1)
    calc
      r ^ s ≤ M ^ s := Real.rpow_le_rpow hr hrM (zero_le_one.trans hs)
      _ ≤ M ^ s * r := by simpa using mul_le_mul_of_nonneg_left h1r (Real.rpow_nonneg (hr.trans hrM) s)
      _ ≤ max 1 (M ^ s) * r := mul_le_mul_of_nonneg_right (le_max_right _ _) hr

theorem admissible_dyadicPopulationFit_taylor_coefficients {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D : ℝ, 0 < D ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ x ∈ unitCube d, ∃ c : AnchoredIndex d C.order → ℝ, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
        (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j)‖ ≤
          D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let E := max 1 (D * (taylorErrorFactor C * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ x hx
  obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family C θ hθ x hx
  refine ⟨c, ?_⟩
  intro j
  let R := taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
    (Real.rpow_nonneg (by positivity) _)
  rw [dyadicPopulationFit_eq_normalized C θ hθ]
  have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx)
    _ _ (dyadicNormalizedDensity_measurable C θ hθ j x) (dyadicNormalizedDensity_bounds C θ hθ j x)
    (dyadicRegressionDifference_continuousOn C θ hθ j x) (dyadicTaylorCoefficients c j)
    R hR (fun w hw => (hc j w hw).1)
  apply h.trans
  calc
    D * R = (D * (taylorErrorFactor C * C.holderBound)) * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by dsimp [R]; ring
    _ ≤ E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

/-- The normalized fitted error vanishes at its anchor with the claimed
Lipschitz factor. The genuine Taylor family supplies both residual premises. -/
theorem admissible_dyadicPopulationFit_spatial_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w - anchoredFitPolynomial (dyadicNormalizedAnchor j x)
        (dyadicPopulationFit (ℓ := C.order) θ j x) w| ≤
          E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
  obtain ⟨D, hD, hpoint⟩ := anchoredPopulationFit_pointwise_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let T := (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial
  have hT : 0 ≤ T := div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _)
    (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  let E := max 1 (T * max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) + D * (taylorErrorFactor C * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ j x hx w hw
  obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family C θ hθ x hx
  let R := taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
    (Real.rpow_nonneg (by positivity) _)
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) x hx
  have hp := hpoint _ hu _ _ (dyadicNormalizedDensity_measurable C θ hθ j x)
    (dyadicNormalizedDensity_bounds C θ hθ j x) (dyadicRegressionDifference_continuousOn C θ hθ j x)
    (dyadicTaylorCoefficients c j) R hR (fun v hv => (hc j v hv).1) w hw
  rw [dyadicPopulationFit_eq_normalized C θ hθ]
  apply hp.trans
  have hrad : euclideanNorm (w - dyadicNormalizedAnchor j x) ≤ Real.sqrt (d : ℝ) := by
    have h := euclideanNorm_le_coordinate_radius (w - dyadicNormalizedAnchor j x) 1 (by norm_num)
      (fun i => by
        change |w i - dyadicNormalizedAnchor j x i| ≤ 1
        exact abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩)
    simpa only [mul_one] using h
  have hs : 1 ≤ C.smoothness := by
    obtain ⟨γ⟩ := (inferInstance : Nonempty (AnchoredIndex d C.order))
    have ho : 1 ≤ C.order := γ.property.1.trans_le γ.property.2
    have hor : (1 : ℝ) ≤ C.order := by exact_mod_cast ho
    exact hor.trans C.order_lt.le
  have hr0 : 0 ≤ euclideanNorm (w - dyadicNormalizedAnchor j x) := by unfold euclideanNorm; positivity
  have hpow := bounded_rpow_le_linear _ _ _ hr0 hrad hs
  calc
    _ ≤ T * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness *
        euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness +
        D * R * euclideanNorm (w - dyadicNormalizedAnchor j x) := add_le_add (hc j w hw).2 le_rfl
    _ ≤ T * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness *
        (max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) * euclideanNorm (w - dyadicNormalizedAnchor j x)) +
        D * R * euclideanNorm (w - dyadicNormalizedAnchor j x) := by gcongr
    _ = (T * max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) + D * (taylorErrorFactor C * C.holderBound)) *
        (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by dsimp [R]; ring
    _ ≤ E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (by positivity) _)) hr0

theorem anchoredTransport_euclidean_norm {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      (1 / 2) * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
  have h := Matrix.l2_opNorm_mulVec (anchoredTransport d ℓ)
    ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c)
  have h' : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      ‖anchoredTransport d ℓ‖ * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
    simpa [EuclideanSpace.equiv] using h
  apply h'.trans
  exact mul_le_mul_of_nonneg_right (anchoredTransport_norm_le_half d ℓ) (norm_nonneg _)

def dyadicPopulationIncrement {d ℓ : ℕ} (θ : RegressionParameter d) (x : Covariate d) :
    ℕ → AnchoredIndex d ℓ → ℝ := anchoredIncrement (fun j => dyadicPopulationFit θ j x)

theorem dyadicPopulationIncrement_error_identity {d ℓ : ℕ} (θ : RegressionParameter d)
    (x : Covariate d) (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    dyadicPopulationIncrement θ x (j + 1) =
      (dyadicPopulationFit θ (j + 1) x - dyadicTaylorCoefficients c (j + 1)) -
        anchoredTransport d ℓ *ᵥ (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j) := by
  rw [dyadicTaylorCoefficients_succ, Matrix.mulVec_sub]
  unfold dyadicPopulationIncrement anchoredIncrement
  abel

theorem dyadic_inverse_scale_succ (j : ℕ) :
    ((2 : ℝ) ^ j)⁻¹ = 2 * ((2 : ℝ) ^ (j + 1))⁻¹ := by
  rw [pow_succ]
  field_simp

theorem admissible_dyadicPopulationIncrement_successor_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ x ∈ unitCube d, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x (j + 1))‖ ≤
        E * (((2 : ℝ) ^ (j + 1))⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hcoeff⟩ := admissible_dyadicPopulationFit_taylor_coefficients C
  let E := D * (1 + (1 / 2) * (2 : ℝ) ^ C.smoothness)
  refine ⟨E, mul_pos hD (by positivity), ?_⟩
  intro θ hθ x hx j
  obtain ⟨c, hc⟩ := hcoeff θ hθ x hx
  let e := fun i => dyadicPopulationFit θ i x - dyadicTaylorCoefficients c i
  rw [dyadicPopulationIncrement_error_identity θ x c j]
  have hsub : ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
      (e (j + 1) - anchoredTransport d C.order *ᵥ e j)‖ ≤
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e (j + 1))‖ +
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e j)‖ := by
    simpa [EuclideanSpace.equiv] using norm_sub_le
      ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e (j + 1)))
      ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e j))
  apply hsub.trans
  have ht := anchoredTransport_euclidean_norm (e j)
  have ht' := ht.trans (mul_le_mul_of_nonneg_left (hc j) (by norm_num : (0 : ℝ) ≤ 1 / 2))
  apply (add_le_add (hc (j + 1)) ht').trans_eq
  rw [dyadic_inverse_scale_succ j, Real.mul_rpow (by norm_num) (by positivity)]
  dsimp [E]
  ring

theorem admissible_dyadicPopulationIncrement_root_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ x ∈ unitCube d,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x 0)‖ ≤ E := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let E := max 1 (D * (2 * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ x hx
  have hres : ∀ w ∈ unitCube d, |dyadicRegressionDifference θ 0 x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor 0 x) (0 : AnchoredIndex d C.order → ℝ) w| ≤
        2 * C.holderBound := by
    intro w hw
    simp only [anchoredFitPolynomial, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    exact (abs_sub _ _).trans (by
      have ha := admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube 0 x w hw)
      have hb := admissible_regression_value_bound C θ hθ x hx
      change |θ.regression (dyadicCellAffine 0 x w)| + |θ.regression x| ≤ _
      linarith)
  have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    (dyadicNormalizedDensity_measurable C θ hθ 0 x) (dyadicNormalizedDensity_bounds C θ hθ 0 x)
    (dyadicRegressionDifference_continuousOn C θ hθ 0 x) 0 (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le) hres
  change ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationFit θ 0 x)‖ ≤ E
  rw [dyadicPopulationFit_eq_normalized C θ hθ]
  simpa only [sub_zero, dyadicNormalizedAnchor, E] using h.trans (le_max_right 1 _)

/-- U2(2), for the actual population fits at every level including the root. -/
theorem admissible_dyadicPopulationIncrement_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ x ∈ unitCube d, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x j)‖ ≤
        E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨E0, hE0, hroot⟩ := admissible_dyadicPopulationIncrement_root_bound C
  obtain ⟨E1, hE1, hsucc⟩ := admissible_dyadicPopulationIncrement_successor_bound C
  refine ⟨max E0 E1, hE0.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ x hx j
  cases j with
  | zero => simpa using (hroot θ hθ x hx).trans (le_max_left E0 E1)
  | succ j =>
    exact (hsucc θ hθ x hx j).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))

theorem dyadicPopulationIncrement_telescope {d ℓ : ℕ} (θ : RegressionParameter d)
    (x z : Covariate d) (J : ℕ) :
    dyadicAnchoredFeature J x z ⬝ᵥ dyadicPopulationFit (ℓ := ℓ) θ J x =
      ∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ dyadicPopulationIncrement (ℓ := ℓ) θ x j :=
  (anchored_increment_telescope (fun j => dyadicPopulationFit θ j x) x z J).symm

end NearlyMinimax
