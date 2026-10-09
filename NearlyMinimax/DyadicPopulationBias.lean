module

public import NearlyMinimax.DyadicIncrementBias
public import NearlyMinimax.DyadicPilotRows
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.InverseDerivativeFamily


@[expose] public section

/-! The true finite multiscale population residual in original U8. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem anchoredFinVector_dotProduct {d ℓ : ℕ} (u v : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector u ⬝ᵥ anchoredFinVector v = u ⬝ᵥ v := by
  simp only [dotProduct, anchoredFinVector, anchoredFinIndex]
  exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp
    (fun γ : AnchoredIndex d ℓ => u γ * v γ)

theorem dyadicPilotRow_dot_coefficients {d ℓ : ℕ} (j : ℕ)
    (x y : Covariate d) (v : AnchoredIndex d ℓ → ℝ) :
    dyadicPilotRow j x y ⬝ᵥ anchoredFinVector v = dyadicAnchoredFeature j x y ⬝ᵥ v :=
  anchoredFinVector_dotProduct _ _

theorem finite_row_abs_dot_le_euclidean_norm {ι : Type*} [Fintype ι]
    (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i, |row i * v i|) ≤ ∑ i, |row i| * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [EuclideanSpace.equiv, Real.norm_eq_abs] using
        PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm v) i
    _ = _ := by rw [Finset.sum_mul]

theorem dyadic_scale_rpow_cancel (j : ℕ) (s : ℝ) :
    (2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹) ^ s = (((2 : ℝ) ^ j)⁻¹) ^ (s - 1) := by
  have h := positive_rpow_times_distance (((2 : ℝ) ^ j)⁻¹) s ((2 : ℝ) ^ j) (by positivity)
  simpa only [inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ j ≠ 0), one_mul, mul_comm] using h

def dyadicPopulationPolynomial {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m (dyadicIncrementRawMean θ j x)

theorem admissible_dyadic_polynomial_row_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x → ∀ m : ℕ,
      |dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) m -
        dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j| ≤
      E * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
        ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m : ℝ) * paperTau C) := by
  obtain ⟨B, hB, herror⟩ := admissible_dyadic_increment_polynomial_error C
  let E := max 1 (B * (anchoredDimension d C.order : ℝ))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ j x hx y hy hcell m
  have hnorm := herror θ hθ j x hx m
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

def dyadicPopulationBiasBudget {d : ℕ} (C : ModelConstants d) (J : ℕ) (m : ℕ → ℕ) : ℝ :=
  (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
    ∑ j ∈ Finset.range (J + 1), (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
      ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m j : ℝ) * paperTau C)

def dyadicPopulationResidual {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (x y : Covariate d) : ℝ :=
  θ.regression y - θ.regression x - ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)

/-- Original U8 finite population bias budget, obtained from the actual U2
telescope and the genuine U5 inverse-polynomial error, for every degree profile. -/
theorem admissible_dyadicPopulationResidual_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x →
        |dyadicPopulationResidual C θ J m x y| ≤
          E * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨A, hA, hfit⟩ := admissible_dyadicPopulationFit_physical_error C
  obtain ⟨B, hB, hpoly⟩ := admissible_dyadic_polynomial_row_error C
  let E := max A B
  refine ⟨E, hA.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ J m x hx y hy hcell
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
  apply (add_le_add (hfit θ hθ J x hx y hy hcell) (Finset.abs_sum_le_sum_abs _ _)).trans
  calc
    _ ≤ A * euclideanNorm (y - x) * (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
        ∑ j ∈ Finset.range (J + 1), B * euclideanNorm (y - x) *
          (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
            Real.exp (-(m j : ℝ) * paperTau C) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_sub_comm]
      exact hpoly θ hθ j x hx y hy
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

end NearlyMinimax
