module

public import NearlyMinimax.PopulationPairBounds


@[expose] public section

/-! Uniform extension-domain constants for the actual population upper proof.
Numerical witnesses are chosen before the open domain; no extension theorem
or fixed-domain admissibility transfer is assumed. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D : ℝ, 0 < D ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d, ∃ c : AnchoredIndex d C.order → ℝ, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
        (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j)‖ ≤
          D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let E := max 1 (D * (taylorErrorFactor C * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx
  obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family (C.withDomain Udom) θ hθ x hx
  refine ⟨c, ?_⟩
  intro j
  let R := taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
    (Real.rpow_nonneg (by positivity) _)
  rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
  have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx)
    _ _ (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x)
    (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ j x) (dyadicTaylorCoefficients c j)
    R hR (fun w hw => (hc j w hw).1)
  apply h.trans
  calc
    D * R = (D * (taylorErrorFactor C * C.holderBound)) * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by dsimp [R]; ring
    _ ≤ E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)


theorem uniform_domain_admissible_dyadicPopulationFit_spatial_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
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
  intro Udom θ hθ j x hx w hw
  obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family (C.withDomain Udom) θ hθ x hx
  let R := taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
    (Real.rpow_nonneg (by positivity) _)
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) x hx
  have hp := hpoint _ hu _ _ (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x)
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ j x)
    (dyadicTaylorCoefficients c j) R hR (fun v hv => (hc j v hv).1) w hw
  rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
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

theorem uniform_domain_admissible_dyadicPopulationIncrement_successor_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x (j + 1))‖ ≤
        E * (((2 : ℝ) ^ (j + 1))⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hcoeff⟩ := uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients C
  let E := D * (1 + (1 / 2) * (2 : ℝ) ^ C.smoothness)
  refine ⟨E, mul_pos hD (by positivity), ?_⟩
  intro Udom θ hθ x hx j
  obtain ⟨c, hc⟩ := hcoeff Udom θ hθ x hx
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

theorem uniform_domain_admissible_dyadicPopulationIncrement_root_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x 0)‖ ≤ E := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let E := max 1 (D * (2 * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx
  have hres : ∀ w ∈ unitCube d, |dyadicRegressionDifference θ 0 x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor 0 x) (0 : AnchoredIndex d C.order → ℝ) w| ≤
        2 * C.holderBound := by
    intro w hw
    simp only [anchoredFitPolynomial, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    exact (abs_sub _ _).trans (by
      have ha := admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube 0 x w hw)
      have hb := admissible_regression_value_bound (C.withDomain Udom) θ hθ x hx
      change |θ.regression (dyadicCellAffine 0 x w)| + |θ.regression x| ≤ _
      dsimp [ModelConstants.withDomain] at ha hb
      linarith)
  have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ 0 x) (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ 0 x)
    (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ 0 x) 0 (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le) hres
  change ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationFit θ 0 x)‖ ≤ E
  rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
  simpa only [sub_zero, dyadicNormalizedAnchor, E] using h.trans (le_max_right 1 _)


theorem uniform_domain_admissible_dyadicPopulationIncrement_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x j)‖ ≤
        E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨E0, hE0, hroot⟩ := uniform_domain_admissible_dyadicPopulationIncrement_root_bound C
  obtain ⟨E1, hE1, hsucc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_successor_bound C
  refine ⟨max E0 E1, hE0.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx j
  cases j with
  | zero => simpa using (hroot Udom θ hθ x hx).trans (le_max_left E0 E1)
  | succ j =>
    exact (hsucc Udom θ hθ x hx j).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))

theorem uniform_domain_admissible_dyadicPopulationFit_physical_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x →
      |θ.regression y - θ.regression x - dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ j x| ≤
        E * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) := by
  obtain ⟨E, hE, hfit⟩ := uniform_domain_admissible_dyadicPopulationFit_spatial_error C
  refine ⟨E, hE, ?_⟩
  intro Udom θ hθ j x hx y hy hcell
  have hw : dyadicNormalizedAnchor j y ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) y hy
  have he := dyadicCellAffine_same_cell j x y hcell
  have h := hfit Udom θ hθ j x hx _ hw
  rw [dyadicPopulationFit_physical_evaluation j x y hcell] at h
  unfold dyadicRegressionDifference at h
  rw [he] at h
  apply h.trans_eq
  have hd := dyadicCellAffine_euclidean_distance j x (dyadicNormalizedAnchor j y)
  rw [he] at hd
  rw [mul_assoc, positive_rpow_times_distance _ _ _ (by positivity), ← hd]
  ring


theorem uniform_domain_admissible_dyadic_increment_polynomial_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ m : ℕ,
      ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) (θ.regression x) m (dyadicIncrementRawMean θ j x) -
            anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
        E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
          Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by
  obtain ⟨χ, hχ, hcond⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := C.order)
  obtain ⟨D, hD, hinc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_bound C
  let E₀ := χ ^ 2 * C.densityUpper ^ (anchoredDimension d C.order + 1) *
    parentInverseErrorConstant C.densityLower C.densityUpper (anchoredDimension d C.order)
  let E := max 1 (E₀ * D)
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ j x hx m
  let u := dyadicNormalizedAnchor j x
  let v := dyadicNormalizedAnchor (j - 1) x
  let p := dyadicNormalizedDensity θ j x
  let q := if j = 0 then (fun _ : Covariate d => (1 : ℝ)) else dyadicNormalizedDensity θ (j - 1) x
  let U := dyadicFinPilotMoments (ℓ := C.order) θ j x
  let V := if j = 0 then 0 else dyadicFinPilotMoments (ℓ := C.order) θ (j - 1) x
  have hqmeas : Measurable q := by
    by_cases hj : j = 0
    · simpa [q, hj, ModelConstants.withDomain] using (measurable_const : Measurable (fun _ : Covariate d => (1 : ℝ)))
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ (j - 1) x
  have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ (j - 1) x
  have hparent : anchoredFinNormalizedGram (ℓ := C.order) v q =
      if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x := by
    by_cases hj : j = 0
    · simp [q, hj, anchoredFinNormalizedGram_one]
    · simp only [q, hj, ite_false]
      exact (dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ (j - 1) x).symm
  have hactual : (anchoredFinNormalizedGram (ℓ := C.order) u p)⁻¹ *ᵥ
      (U false - θ.regression x • U true) - anchoredFinTransport d C.order *ᵥ
        ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
    rw [hparent, ← dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ j x]
    exact dyadicFinite_increment_eq_actual (C.withDomain Udom) θ hθ j x hx
  have hsmall : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
      ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - θ.regression x • U true) -
        anchoredFinTransport d C.order *ᵥ
          ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)))‖ ≤
      D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
    rw [hactual, anchoredFinVector_norm]
    exact hinc Udom θ hθ x hx j
  have he := anchoredNormalized_increment_error u v p q
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqmeas
    C.densityLower C.densityUpper χ (D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness)
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
    (hcond u (gridNormalizedAnchor_mem_cube _ (by positivity) x hx))
    U V (θ.regression x) (anchoredFinTransport d C.order) hsmall m
  rw [hactual] at he
  have hval : dyadicIncrementRawMean (ℓ := C.order) θ j x = fun a =>
      incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
        ((Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a) := by
    rw [dyadicIncrementRawMean_eq_population (C.withDomain Udom) θ hθ j x hx]
    have hcurrent : anchoredFinNormalizedGram (ℓ := C.order) u p = dyadicFinPilotGram θ j x :=
      (dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ j x).symm
    simp only [dyadicIncrementPopulation, hparent, hcurrent]
    rfl
  rw [hval, incrementFinVector_eval_population]
  calc
    _ ≤ E₀ * (D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness) * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
        Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := he
    _ = (E₀ * D) * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
        Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by ring
    _ ≤ E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
        Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by
      gcongr
      exact le_max_right _ _

theorem uniform_domain_admissible_dyadic_polynomial_row_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x → ∀ m : ℕ,
      |dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) m -
        dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j| ≤
      E * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
        ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m : ℝ) * paperTau C) := by
  obtain ⟨B, hB, herror⟩ := uniform_domain_admissible_dyadic_increment_polynomial_error C
  let E := max 1 (B * (anchoredDimension d C.order : ℝ))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ j x hx y hy hcell m
  have hnorm := herror Udom θ hθ j x hx m
  rw [exteriorTau_sqrt_ratio C.densityLower C.densityUpper C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper)] at hnorm
  change ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
    (dyadicPopulationPolynomial C θ j x (θ.regression x) m -
      anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
    B * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
      Real.exp (-(m : ℝ) * paperTau C) at hnorm
  rw [← dyadicPilotRow_dot_coefficients, ← dotProduct_sub]
  apply (finite_row_abs_dot_le_euclidean_norm _ _).trans
  have hr := dyadicPilotRow_sum_abs_le_distance (ℓ := C.order) j x y hx hy hcell
  have hd : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
  calc
    _ ≤ ((anchoredDimension d C.order : ℝ) * (2 : ℝ) ^ j * euclideanNorm (y - x)) *
        (B * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
          Real.exp (-(m : ℝ) * paperTau C)) := mul_le_mul hr hnorm (norm_nonneg _) (by positivity)
    _ = (B * (anchoredDimension d C.order : ℝ)) * euclideanNorm (y - x) *
        ((2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness) *
          ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m : ℝ) * paperTau C) := by ring
    _ = (B * (anchoredDimension d C.order : ℝ)) * euclideanNorm (y - x) *
        (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
          ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m : ℝ) * paperTau C) := by
      rw [dyadic_scale_rpow_cancel]
    _ ≤ E * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
        ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m : ℝ) * paperTau C) := by
      gcongr
      exact le_max_right _ _

theorem uniform_domain_admissible_dyadicPopulationResidual_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x →
        |dyadicPopulationResidual C θ J m x y| ≤
          E * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨A, hA, hfit⟩ := uniform_domain_admissible_dyadicPopulationFit_physical_error C
  obtain ⟨B, hB, hpoly⟩ := uniform_domain_admissible_dyadic_polynomial_row_error C
  let E := max A B
  refine ⟨E, hA.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ J m x hx y hy hcell
  have hd : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
  have heq : dyadicPopulationResidual C θ J m x y =
      (θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x) +
      ∑ j ∈ Finset.range (J + 1), (dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j -
        dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) := by
    rw [dyadicPopulationIncrement_telescope, Finset.sum_sub_distrib]
    unfold dyadicPopulationResidual
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply (add_le_add (hfit Udom θ hθ J x hx y hy hcell) (Finset.abs_sum_le_sum_abs _ _)).trans
  calc
    _ ≤ A * euclideanNorm (y - x) * (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
        ∑ j ∈ Finset.range (J + 1), B * euclideanNorm (y - x) *
          (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
            Real.exp (-(m j : ℝ) * paperTau C) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_sub_comm]
      exact hpoly Udom θ hθ j x hx y hy
        (dyadicPilotCell_subset_coarser j J (by exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x hcell) (m j)
    _ ≤ E * euclideanNorm (y - x) * (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
        ∑ j ∈ Finset.range (J + 1), E * euclideanNorm (y - x) *
          (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
            Real.exp (-(m j : ℝ) * paperTau C) := by
      apply add_le_add
      · gcongr
        exact le_max_left _ _
      · apply Finset.sum_le_sum
        intro j _
        gcongr
        exact le_max_right _ _
    _ = E * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
      unfold dyadicPopulationBiasBudget
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring


theorem uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound {d : ℕ} (C : ModelConstants d) :
    ∃ W : ℝ, 0 < W ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool,
        ‖dyadicFinPilotMoments (ℓ := C.order) θ j x t‖ ≤ W := by
  obtain ⟨W, hW, hb⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := C.order)
    C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  refine ⟨W, hW, ?_⟩
  intro Udom θ hθ j x hx t
  rw [dyadicFinPilotMoments_eq_anchored (C.withDomain Udom) θ hθ j x hx]
  exact hb _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    ((dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x).mono
      (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩))
    (fun w hw => admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube j x w hw)) t

theorem uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ B : ℝ, 0 < B ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m : ℕ,
        ‖dyadicPopulationPolynomial C θ j x y m‖ ≤ B := by
  obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W Y C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, hB, ?_⟩
  intro Udom θ hθ j x hx y hy m
  let q := if j = 0 then (fun _ : Covariate d => (1 : ℝ)) else dyadicNormalizedDensity θ (j - 1) x
  have hqm : Measurable q := by
    by_cases hj : j = 0
    · simpa [q, hj, ModelConstants.withDomain] using (measurable_const : Measurable (fun _ : Covariate d => (1 : ℝ)))
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ (j - 1) x
  have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ (j - 1) x
  have hV (t : Bool) : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
      else dyadicFinPilotMoments θ (j - 1) x) t‖ ≤ W := by
    by_cases hj : j = 0
    · simpa [hj] using hW.le
    · simpa only [hj, ite_false] using hmom Udom θ hθ (j - 1) x hx t
  have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ (j - 1)) (by positivity) x hx)
    (dyadicNormalizedDensity θ j x) q
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqm
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
    (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
    (hmom Udom θ hθ j x hx) hV y hy m 0 (fun i => Fin.elim0 i)
  rw [← dyadicIncrementRawMean_eq_with_virtual_parent (C.withDomain Udom) θ hθ j x hx] at hd
  simpa only [dyadicPopulationPolynomial, iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
    Fin.prod_univ_zero] using hd

theorem uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ B : ℝ, 0 < B ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool, ∀ m : ℕ,
        ‖dyadicPopulationRawPolynomial C θ j x t m‖ ≤ B := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨B, hB, hb⟩ := uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound C 1 zero_le_one
  refine ⟨2 * B, mul_pos (by norm_num) hB, ?_⟩
  intro Udom θ hθ j x hx t m
  have h0 := hb Udom θ hθ j x hx 0 (by norm_num) m
  have h1 := hb Udom θ hθ j x hx 1 (by norm_num) m
  have he0 : dyadicPopulationRawPolynomial C θ j x false m = dyadicPopulationPolynomial C θ j x 0 m := by
    rw [dyadicPopulationPolynomial_affine, zero_smul, sub_zero]
  cases t
  · have hf : ‖dyadicPopulationRawPolynomial C θ j x false m‖ ≤ B := by rw [he0]; exact h0
    exact hf.trans (by linarith)
  · have he : dyadicPopulationRawPolynomial C θ j x true m =
        dyadicPopulationPolynomial C θ j x 0 m - dyadicPopulationPolynomial C θ j x 1 m := by
      rw [dyadicPopulationPolynomial_affine, dyadicPopulationPolynomial_affine]
      simp only [zero_smul, sub_zero, one_smul]
      abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)

theorem uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ∀ t : Bool, |dyadicPopulationPilotSum C θ J m t (x, y)| ≤ R := by
  obtain ⟨B, hB, hb⟩ := uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound C hs
  let R := (2 * (anchoredDimension d C.order : ℝ) * Real.sqrt (d : ℝ)) * B
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  intro Udom θ hθ J m x hx y hy hcell t
  unfold dyadicPopulationPilotSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), (∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
      apply Finset.sum_le_sum
      intro j hj
      exact (finite_row_abs_dot_le_pi_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hb Udom θ hθ j x hx t (m j)) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    _ = (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
      rw [Finset.sum_mul]
    _ ≤ R := mul_le_mul_of_nonneg_right (dyadicPilotRow_total_abs_le J x y hx hy hcell) hB.le

theorem uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ‖dyadicPopulationCoefficients C θ J m (x, y)‖ ≤ Cp := by
  obtain ⟨R, hR, hb⟩ := uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound C hs
  refine ⟨Real.sqrt 3 * (1 + R), mul_pos (by positivity) (by positivity), ?_⟩
  intro Udom θ hθ J m x hx y hy hc
  have ht := hb Udom θ hθ J m x hx y hy hc true
  have hf := hb Udom θ hθ J m x hx y hy hc false
  have hcoord (i : Fin 3) : |dyadicPopulationCoefficients C θ J m (x, y) i| ≤ 1 + R := by
    fin_cases i
    · simpa [dyadicPopulationCoefficients] using hR
    · change |-1 + dyadicPopulationPilotSum C θ J m true (x, y)| ≤ 1 + R
      exact (abs_add_le _ _).trans (by simpa using add_le_add_left ht 1)
    · change |-dyadicPopulationPilotSum C θ J m false (x, y)| ≤ 1 + R
      rw [abs_neg]
      exact hf.trans (by linarith)
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc
    (∑ i : Fin 3, ‖dyadicPopulationCoefficients C θ J m (x, y) i‖ ^ 2) ≤ ∑ _i : Fin 3, (1 + R) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hcoord i) 2
    _ = 3 * (1 + R) ^ 2 := by simp
    _ = (Real.sqrt 3 * (1 + R)) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]

end NearlyMinimax
