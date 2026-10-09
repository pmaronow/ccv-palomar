module

public import NearlyMinimax.DyadicMeasurability
public import NearlyMinimax.AnchoredCard


@[expose] public section

/-! The three original U2 conclusions for the actual population coefficients,
with feature nonemptiness derived from the paper's s>1 regime. -/

noncomputable section
open Set Matrix
open scoped BigOperators
namespace NearlyMinimax

theorem anchoredIndex_nonempty_of_one_lt_smoothness {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) : Nonempty (AnchoredIndex d C.order) := by
  have horder : 0 < C.order := by
    by_contra h
    have hz : C.order = 0 := by omega
    have hle := C.smoothness_le_order_add_one
    simp only [hz, Nat.cast_zero, zero_add] at hle
    linarith
  exact anchoredIndex_nonempty C.dimension_pos horder

/-- Original lemma U2, including its physical spatial error, root increment,
and exact finite telescope. There are no approximation or risk premises. -/
theorem paper_population_fit {d : ℕ} (C : ModelConstants d) (hs : 1 < C.smoothness) :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ x ∈ unitCube d,
      (∀ j : ℕ, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x →
        |θ.regression y - θ.regression x -
          dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ j x| ≤
            E * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1)) ∧
      (∀ j : ℕ, ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
        (dyadicPopulationIncrement θ x j)‖ ≤ E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness) ∧
      (∀ (J : ℕ) (y : Covariate d),
        dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x =
          ∑ j ∈ Finset.range (J + 1),
            dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j) := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨A, hA, ha⟩ := admissible_dyadicPopulationFit_physical_error C
  obtain ⟨B, hB, hb⟩ := admissible_dyadicPopulationIncrement_bound C
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ x hx
  refine ⟨?_, ?_, ?_⟩
  · intro j y hy hcell
    exact (ha θ hθ j x hx y hy hcell).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left A B) (by unfold euclideanNorm; positivity))
        (Real.rpow_nonneg (by positivity) _))
  · intro j
    exact (hb θ hθ x hx j).trans
      (mul_le_mul_of_nonneg_right (le_max_right A B) (Real.rpow_nonneg (by positivity) _))
  · intro J y
    exact dyadicPopulationIncrement_telescope θ x y J

end NearlyMinimax
