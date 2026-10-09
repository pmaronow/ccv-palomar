module

public import NearlyMinimax.IncrementPilotFeatures
public import NearlyMinimax.PopulationRowDerivatives
public import NearlyMinimax.DyadicFit


@[expose] public section

/-! Actual original-law factorial pilots at a dyadic anchor.  Their population
point and derivative constants are derived from the original admissibility
conditions, rather than supplied as stochastic budget assumptions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem dyadicFinPilotMoments_eq_anchored {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    dyadicFinPilotMoments (ℓ := ℓ) θ j x = anchoredFinMomentFamilies
      (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
      (θ.regression ∘ dyadicCellAffine j x) := by
  funext t i
  exact dyadicFinPilotMoments_eq_normalized C θ hθ j x hx t i

theorem dyadicIncrementRawMean_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (hj : j ≠ 0)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor (j - 1) x) (dyadicNormalizedDensity θ (j - 1) x))
        (anchoredFinMomentFamilies (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
          (θ.regression ∘ dyadicCellAffine j x))
        (anchoredFinMomentFamilies (dyadicNormalizedAnchor (j - 1) x) (dyadicNormalizedDensity θ (j - 1) x)
          (θ.regression ∘ dyadicCellAffine (j - 1) x))
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx]
  simp only [dyadicIncrementPopulation, if_neg hj,
    dyadicFinPilotGram_eq_normalized C θ hθ,
    dyadicFinPilotMoments_eq_anchored C θ hθ j x hx,
    dyadicFinPilotMoments_eq_anchored C θ hθ (j - 1) x hx]

/-- Uniform genuine derivative operator bounds at the true free-moment mean
of the actual current/parent observations. -/
theorem admissible_dyadic_increment_derivative_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ j : ℕ, j ≠ 0 →
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤
          (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k := by
  obtain ⟨D, A, hD, hA, hder⟩ := anchored_actual_population_row_derivative_operator_bound
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper C.holderBound C.holderBound
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
    C.holderBound_pos.le C.holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro θ hθ j hj x hx y hy m k row
  rw [dyadicIncrementRawMean_eq_normalized C θ hθ j hj x hx]
  exact hder _ _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx)
    (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _ _ _
    (dyadicNormalizedDensity_measurable C θ hθ j x)
    (dyadicNormalizedDensity_measurable C θ hθ (j - 1) x)
    (dyadicNormalizedDensity_bounds C θ hθ j x)
    (dyadicNormalizedDensity_bounds C θ hθ (j - 1) x)
    (fun w hw => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube j x w hw))
    (fun w hw => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube (j - 1) x w hw))
    y hy m k row

def rowIncrementPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  ∑ i, C (row i) * incrementFinPolynomial r a b T y m i

theorem rowIncrementPolynomial_eval (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) (z : Fin (Fintype.card (incrementVariables r)) → ℝ) :
    eval z (rowIncrementPolynomial r a b T y m row) = incrementFinScalar r a b T y m row z := by
  simp [rowIncrementPolynomial, incrementFinScalar, incrementFinVector, dotProduct]

theorem rowIncrementPolynomial_degree (r : ℕ) [NeZero r] (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (rowIncrementPolynomial r a b T y m row).totalDegree ≤ m + r + 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add, incrementFinPolynomial] using
    (totalDegree_rename_le _ _).trans (incrementEntryPolynomial_degree r a b T y m i)

theorem anchoredFinNormalizedGram_one {d ℓ : ℕ} (u : Covariate d) :
    anchoredFinNormalizedGram (ℓ := ℓ) u (fun _ => 1) = 1 := by
  have hG : anchoredDensityGram (ℓ := ℓ) u (fun _ => 1) = anchoredGram u := by
    ext γ δ
    simp [anchoredDensityGram, anchoredGram]
  unfold anchoredFinNormalizedGram
  rw [hG, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_posDef u).isUnit)]
  exact map_one _

theorem dyadicIncrementRawMean_root_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (x : Covariate d) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ 0 x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (fun _ => 1))
        (anchoredFinMomentFamilies (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x)
          (θ.regression ∘ dyadicCellAffine 0 x)) 0
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ 0 x hx]
  simp only [dyadicIncrementPopulation, ite_true, anchoredFinNormalizedGram_one,
    dyadicFinPilotGram_eq_normalized C θ hθ, dyadicFinPilotMoments_eq_anchored C θ hθ 0 x hx]

/-- The deterministic virtual parent is a genuine unit-density normalized
Gram with zero vector families; its derivative constants are uniform too. -/
theorem admissible_dyadic_increment_root_derivative_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ x ∈ unitCube d,
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ 0 x)‖ ≤
          (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k := by
  have hb : 0 ≤ C.densityUpper := zero_le_one.trans C.one_lt_densityUpper.le
  obtain ⟨W, hW, hmom⟩ := anchoredFinMomentFamilies_uniform_bound
    (d := d) (ℓ := C.order) C.densityUpper C.holderBound hb C.holderBound_pos.le
  obtain ⟨D, A, hD, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W C.holderBound
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le C.holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro θ hθ x hx y hy m k row
  have hu : dyadicNormalizedAnchor 0 x ∈ unitCube d :=
    gridNormalizedAnchor_mem_cube _ (by positivity) x hx
  have hp := dyadicNormalizedDensity_bounds C θ hθ 0 x
  have hf : ∀ w ∈ unitCube d, |(θ.regression ∘ dyadicCellAffine 0 x) w| ≤ C.holderBound :=
    fun w hw => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube 0 x w hw)
  have hU := hmom _ hu _ _
    (hp.mono (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩)) hf
  have hV (t : Bool) : ‖(0 : Bool → Fin (anchoredDimension d C.order) → ℝ) t‖ ≤ W := by
    simpa using hW.le
  have hrow : 0 ≤ ∑ i, |row i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro directions
  rw [incrementFinScalar_iteratedFDeriv, dyadicIncrementRawMean_root_eq_normalized C θ hθ x hx]
  have hd := hder _ _ hu hu _ (fun _ => 1)
    (dyadicNormalizedDensity_measurable C θ hθ 0 x) measurable_const hp
    (Filter.Eventually.of_forall (fun _ => ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩))
    _ 0 hU hV y hy m k directions
  calc
    _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m)
        (fun a => incrementValuation
          (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x))
          (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (fun _ => 1))
          (anchoredFinMomentFamilies (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x)
            (θ.regression ∘ dyadicCellAffine 0 x)) 0
          ((Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a)) directions‖ :=
      (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖directions i‖) :=
      mul_le_mul (rowFunctional_norm_le row) hd (norm_nonneg _) hrow
    _ = ((∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k) * ∏ i, ‖directions i‖ := by ring

theorem admissible_dyadic_increment_all_derivative_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤
          (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k := by
  obtain ⟨D₀, A₀, hD₀, hA₀, hroot⟩ := admissible_dyadic_increment_root_derivative_bound C
  obtain ⟨D₁, A₁, hD₁, hA₁, hnext⟩ := admissible_dyadic_increment_derivative_bound C
  refine ⟨max D₀ D₁, max A₀ A₁, hD₀.trans_le (le_max_left _ _), hA₀.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ j x hx y hy m k row
  have hrow : 0 ≤ ∑ i, |row i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  by_cases hj : j = 0
  · subst j
    apply (hroot θ hθ x hx y hy m k row).trans
    gcongr <;> exact le_max_left _ _
  · apply (hnext θ hθ j hj x hx y hy m k row).trans
    gcongr <;> exact le_max_right _ _

def dyadicPolynomialPilot {d : ℕ} (C : ModelConstants d) (n j : ℕ) (x : Covariate d)
    (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ)
    (z : Fin n → Observation d) : ℝ :=
  RoughRegime.Upper.polynomialLift
    (rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m row)
    (fun i z => dyadicIncrementRawVector j x (z i)) z

/-- The concrete coefficient lift is L² and exactly unbiased at its genuine
population polynomial, even though the observed responses are unbounded. -/
theorem dyadicPolynomialPilot_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (dyadicPolynomialPilot C n j x y m row) 2 (sampleLaw θ n) ∧
    (∫ z, dyadicPolynomialPilot C n j x y m row z ∂sampleLaw θ n) =
      incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  refine ⟨LiftL2.polynomialLift_memLp_two_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hind hmeas hL2, ?_⟩
  rw [← rowIncrementPolynomial_eval]
  exact LiftL2.polynomialLift_expectation_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hind hmeas hid hL2 hmean

/-- The actual pointwise pilot variance satisfies the U6 factorial series.
All stochastic moment and derivative bounds in this endpoint are consequences
of original-model admissibility. -/
theorem admissible_dyadicPolynomialPilot_variance {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
      m + anchoredDimension d C.order + 1 ≤ n →
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
        variance (dyadicPolynomialPilot C n j x y m row) (sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 *
            ∑ t : Fin (m + anchoredDimension d C.order + 1),
              ((t.val + 1).factorial : ℝ) *
                (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
                  preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (t.val + 1) := by
  obtain ⟨D, A, hD, hA, hder⟩ := admissible_dyadic_increment_all_derivative_bound C
  refine ⟨D, A, hD, hA, ?_⟩
  intro θ hθ n j x hx y hy m row hdegree Λ hΛ hΛn
  let := sampleLaw_isProbability C θ hθ n
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := C.order) j x (z i)
  let E := (Fintype.card (incrementVariables (anchoredDimension d C.order)) : ℝ) *
    preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j
  have hE : 0 ≤ E := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
      (dyadicPilotScale_pos _ _).le
  have hrow : 0 ≤ (∑ i, |row i|) * D :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  have hv := LiftL2.polynomialLift_variance_le_raw_power_l2 F X (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hind hmeas hid hL2 hmean Λ hΛ
    (by simpa only [Nat.cast_add, Nat.cast_one] using hΛn)
  apply hv.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt t.isLt).trans hdegree)
  have hFeval : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
  have hd : ‖iteratedFDeriv ℝ (t.val + 1) (fun z => eval z F) (dyadicIncrementRawMean θ j x)‖ ≤
      ((∑ i, |row i|) * D) * ((t.val + 1).factorial : ℝ) * A ^ (t.val + 1) := by
    rw [hFeval]
    exact hder θ hθ j x hx y hy m (t.val + 1) row
  have hb := KernelMomentBounds.factorial_kernel_budget
    (iteratedFDeriv ℝ (t.val + 1) (fun z => eval z F) (dyadicIncrementRawMean θ j x))
    (fun i => X (e i)) (hind.precomp e.injective) (fun i => hmeas (e i))
    (fun i a => hL2 (e i) a) E ((∑ i, |row i|) * D) A Λ hE hrow hA.le hΛ
    (fun i => dyadicIncrementRawVector_sample_second_le C θ hθ j x hx (e i)) hd
  simpa only [E, e, mul_assoc] using hb

end NearlyMinimax
