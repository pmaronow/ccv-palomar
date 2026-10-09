module

public import NearlyMinimax.DyadicPopulationBias
public import NearlyMinimax.ResponseOperators


@[expose] public section

/-! Actual uniformly bounded multiscale population coefficient fields. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem admissible_dyadicFinPilotMoments_uniform_bound {d : ℕ} (C : ModelConstants d) :
    ∃ W : ℝ, 0 < W ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool,
        ‖dyadicFinPilotMoments (ℓ := C.order) θ j x t‖ ≤ W := by
  obtain ⟨W, hW, hb⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := C.order)
    C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  refine ⟨W, hW, ?_⟩
  intro θ hθ j x hx t
  rw [dyadicFinPilotMoments_eq_anchored C θ hθ j x hx]
  exact hb _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    ((dyadicNormalizedDensity_bounds C θ hθ j x).mono
      (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩))
    (fun w hw => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube j x w hw)) t

theorem dyadicIncrementRawMean_eq_with_virtual_parent {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor (j - 1) x)
          (if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x))
        (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx]
  unfold dyadicIncrementPopulation
  rw [dyadicFinPilotGram_eq_normalized C θ hθ j x]
  by_cases hj : j = 0
  · simp [hj, anchoredFinNormalizedGram_one]
  · simp only [hj, ite_false]
    rw [dyadicFinPilotGram_eq_normalized C θ hθ (j - 1) x]

/-- Uniform order-zero inverse-polynomial bound at true original-law means.
The response range is arbitrary and fixed, so `Y=1` covers the true slope
even when the model's regression bound is smaller than one. -/
theorem admissible_dyadicPopulationPolynomial_uniform_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ B : ℝ, 0 < B ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m : ℕ,
        ‖dyadicPopulationPolynomial C θ j x y m‖ ≤ B := by
  obtain ⟨W, hW, hmom⟩ := admissible_dyadicFinPilotMoments_uniform_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W Y C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, hB, ?_⟩
  intro θ hθ j x hx y hy m
  let q := if j = 0 then (fun _ : Covariate d => (1 : ℝ)) else dyadicNormalizedDensity θ (j - 1) x
  have hqm : Measurable q := by
    by_cases hj : j = 0
    · simpa [q, hj] using (measurable_const : Measurable (fun _ : Covariate d => (1 : ℝ)))
    · simpa [q, hj] using dyadicNormalizedDensity_measurable C θ hθ (j - 1) x
  have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa [q, hj] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
    · simpa [q, hj] using dyadicNormalizedDensity_bounds C θ hθ (j - 1) x
  have hV (t : Bool) : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
      else dyadicFinPilotMoments θ (j - 1) x) t‖ ≤ W := by
    by_cases hj : j = 0
    · simpa [hj] using hW.le
    · simpa only [hj, ite_false] using hmom θ hθ (j - 1) x hx t
  have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ (j - 1)) (by positivity) x hx)
    (dyadicNormalizedDensity θ j x) q
    (dyadicNormalizedDensity_measurable C θ hθ j x) hqm
    (dyadicNormalizedDensity_bounds C θ hθ j x) hqb
    (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
    (hmom θ hθ j x hx) hV y hy m 0 (fun i => Fin.elim0 i)
  rw [← dyadicIncrementRawMean_eq_with_virtual_parent C θ hθ j x hx] at hd
  simpa only [dyadicPopulationPolynomial, iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
    Fin.prod_univ_zero] using hd

def dyadicPopulationRawPolynomial {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (t : Bool) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinRawVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) t m (dyadicIncrementRawMean θ j x)

theorem dyadicPopulationPolynomial_affine {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) :
    dyadicPopulationPolynomial C θ j x y m = dyadicPopulationRawPolynomial C θ j x false m -
      y • dyadicPopulationRawPolynomial C θ j x true m := by
  exact congrFun (incrementFinVector_affine _ _ _ _ y m) (dyadicIncrementRawMean θ j x)

theorem admissible_dyadicPopulationRawPolynomial_uniform_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ B : ℝ, 0 < B ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool, ∀ m : ℕ,
        ‖dyadicPopulationRawPolynomial C θ j x t m‖ ≤ B := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨B, hB, hb⟩ := admissible_dyadicPopulationPolynomial_uniform_bound C 1 zero_le_one
  refine ⟨2 * B, mul_pos (by norm_num) hB, ?_⟩
  intro θ hθ j x hx t m
  have h0 := hb θ hθ j x hx 0 (by norm_num) m
  have h1 := hb θ hθ j x hx 1 (by norm_num) m
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

end NearlyMinimax
