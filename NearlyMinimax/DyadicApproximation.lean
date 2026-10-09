module

public import NearlyMinimax.DyadicFitBounds


@[expose] public section

/-! U2's approximation bound in the original physical cell coordinates. -/

noncomputable section
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem dyadicCellAffine_same_cell {d : ℕ} (j : ℕ) (x y : Covariate d)
    (hcell : y ∈ dyadicPilotCell j x) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j y) = y := by
  have hc : regularGridCell ((2 : ℕ) ^ j) (by positivity) y =
      regularGridCell ((2 : ℕ) ^ j) (by positivity) x := hcell
  simpa only [dyadicCellAffine, hc] using dyadicCellAffine_anchor j y

theorem dyadicPopulationFit_physical_evaluation {d ℓ : ℕ} (j : ℕ)
    (x y : Covariate d) (hcell : y ∈ dyadicPilotCell j x) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredFitPolynomial (dyadicNormalizedAnchor j x) c (dyadicNormalizedAnchor j y) =
      dyadicAnchoredFeature j x y ⬝ᵥ c := by
  have he := dyadicCellAffine_same_cell j x y hcell
  unfold anchoredFitPolynomial dotProduct
  apply Finset.sum_congr rfl
  intro γ _
  have h := dyadicAnchoredFeature_affine j x (dyadicNormalizedAnchor j y) γ
  change dyadicAnchoredFeature j x (dyadicCellAffine j x (dyadicNormalizedAnchor j y)) γ = _ at h
  rw [he] at h
  change dyadicAnchoredFeature j x y γ =
    anchoredFeature (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor j y) γ at h
  rw [h]
  ring

theorem positive_rpow_times_distance (h s r : ℝ) (hh : 0 < h) :
    h ^ s * r = (h * r) * h ^ (s - 1) := by
  have he : s = (s - 1) + 1 := by ring
  conv_lhs => rw [he, Real.rpow_add hh, Real.rpow_one]
  ring

/-- Original U2(1): the true fitted increment has error proportional to the
physical distance, with scale `2^(-j(s-1))`, uniformly over admissible models. -/
theorem admissible_dyadicPopulationFit_physical_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x →
      |θ.regression y - θ.regression x - dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ j x| ≤
        E * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) := by
  obtain ⟨E, hE, hfit⟩ := admissible_dyadicPopulationFit_spatial_error C
  refine ⟨E, hE, ?_⟩
  intro θ hθ j x hx y hy hcell
  have hw : dyadicNormalizedAnchor j y ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) y hy
  have he := dyadicCellAffine_same_cell j x y hcell
  have h := hfit θ hθ j x hx _ hw
  rw [dyadicPopulationFit_physical_evaluation j x y hcell] at h
  unfold dyadicRegressionDifference at h
  rw [he] at h
  apply h.trans_eq
  have hd := dyadicCellAffine_euclidean_distance j x (dyadicNormalizedAnchor j y)
  rw [he] at hd
  rw [mul_assoc, positive_rpow_times_distance _ _ _ (by positivity), ← hd]
  ring

/-- The known preconditioner cancels in the genuine inverse population fit. -/
theorem dyadicPopulationFit_preconditioner_cancels {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    (dyadicPreconditionedGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      ((dyadicKnownGram j x)⁻¹ *ᵥ (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)) =
        dyadicPopulationFit θ j x := by
  have hB := (Matrix.isUnit_iff_isUnit_det _).mp (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit
  letI := (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit.invertible
  unfold dyadicPreconditionedGram dyadicPopulationFit
  rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.mulVec_mulVec,
    Matrix.mul_assoc _ (dyadicKnownGram j x) (dyadicKnownGram j x)⁻¹,
    Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]

end NearlyMinimax
