module

public import NearlyMinimax.AffineCells
public import NearlyMinimax.PopulationMomentDerivatives


@[expose] public section

/-! Original-law dyadic Grams and their exact normalized whitening charts. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace NearlyMinimax

def dyadicNormalizedAnchor {d : ℕ} (j : ℕ) (x : Covariate d) : Covariate d :=
  gridNormalizedAnchor ((2 : ℕ) ^ j) (by positivity) x

def dyadicCellAffine {d : ℕ} (j : ℕ) (x w : Covariate d) : Covariate d :=
  gridAffine ((2 : ℕ) ^ j) (regularGridCell _ (by positivity) x) w

def dyadicNormalizedDensity {d : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ := θ.density ∘ dyadicCellAffine j x

def dyadicKnownGram {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂cubeVolume d

def dyadicPopulationGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ

def dyadicPreconditionedGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (dyadicKnownGram j x)⁻¹ * dyadicPopulationGram θ j x

theorem admissible_designLaw_setIntegral {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (s : Set (Covariate d)) (hs : MeasurableSet s) (f : Covariate d → ℝ) :
    (∫ z in s, f z ∂designLaw θ) = ∫ z in s, θ.density z * f z ∂cubeVolume d := by
  unfold designLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (hθ.1.ennreal_ofReal.aemeasurable) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hθ.2.2.1] with z hz
  rw [ENNReal.toReal_ofReal (C.densityLower_pos.le.trans hz.1)]
  rfl

theorem dyadicKnownGram_eq_normalized {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicKnownGram (ℓ := ℓ) j x = anchoredGram (dyadicNormalizedAnchor j x) := by
  ext γ δ
  have h := regular_grid_cell_integral ((2 : ℕ) ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicKnownGram, dyadicPilotScale,
    dyadicPilotCell, Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine,
    anchoredGram, dyadicNormalizedAnchor] using h

theorem dyadicPopulationGram_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicPopulationGram (ℓ := ℓ) θ j x =
      anchoredDensityGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  ext γ δ
  change dyadicPilotScale d j * (∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ) = _
  rw [admissible_designLaw_setIntegral C θ hθ _ (dyadicPilotCell_measurable j x)]
  have h := regular_grid_cell_integral ((2 : ℕ) ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => θ.density z * (dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ))
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicPilotScale, dyadicPilotCell,
    Set.preimage, Set.mem_singleton_iff, dyadicAnchoredFeature_affine, anchoredDensityGram,
    dyadicNormalizedAnchor, dyadicNormalizedDensity, Function.comp_apply, dyadicCellAffine] using h

theorem dyadicNormalizedDensity_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    Measurable (dyadicNormalizedDensity θ j x) :=
  hθ.1.comp (gridAffineEquiv _ (by positivity) _).measurable

theorem dyadicNormalizedDensity_bounds {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper :=
  gridAffine_ae_pullback _ (by positivity) _ hθ.2.2.1

theorem dyadicKnownGram_posDef {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    (dyadicKnownGram (ℓ := ℓ) j x).PosDef := by
  rw [dyadicKnownGram_eq_normalized]
  exact anchoredGram_posDef _

theorem dyadicPopulationGram_sandwich {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    (dyadicPopulationGram (ℓ := ℓ) θ j x - C.densityLower • dyadicKnownGram j x).PosSemidef ∧
      (C.densityUpper • dyadicKnownGram (ℓ := ℓ) j x - dyadicPopulationGram θ j x).PosSemidef := by
  rw [dyadicPopulationGram_eq_normalized C θ hθ, dyadicKnownGram_eq_normalized]
  exact anchoredDensityGram_sandwich _ _ (dyadicNormalizedDensity_measurable C θ hθ j x)
    _ _ C.densityLower_pos.le (dyadicNormalizedDensity_bounds C θ hθ j x)

theorem dyadicPopulationGram_posDef {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    (dyadicPopulationGram (ℓ := ℓ) θ j x).PosDef := by
  rw [dyadicPopulationGram_eq_normalized C θ hθ]
  exact anchoredDensityGram_posDef _ _ (dyadicNormalizedDensity_measurable C θ hθ j x)
    _ _ C.densityLower_pos (dyadicNormalizedDensity_bounds C θ hθ j x)

/-- The actual original-law dyadic matrix is similar to a Hermitian matrix
whose spectrum lies in the original density interval. -/
theorem dyadicPreconditionedGram_spectral_chart {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    let Q := anchoredSimilarityUnit (ℓ := ℓ) (dyadicNormalizedAnchor j x)
    let S := Q⁻¹.val * dyadicPreconditionedGram θ j x * Q.val
    S.IsHermitian ∧ spectrum ℝ S ⊆ Icc C.densityLower C.densityUpper := by
  dsimp
  rw [dyadicPreconditionedGram, dyadicKnownGram_eq_normalized,
    dyadicPopulationGram_eq_normalized C θ hθ, anchored_preconditioned_similarity]
  exact ⟨anchoredWhitenedGram_isHermitian _ _, anchoredWhitenedGram_spectrum _ _
    (dyadicNormalizedDensity_measurable C θ hθ j x) _ _ C.densityLower_pos.le
    (dyadicNormalizedDensity_bounds C θ hθ j x)⟩

theorem dyadicSimilarityUnit_uniform_condition {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)] :
    ∃ χ : ℝ, 0 < χ ∧ ∀ j : ℕ, ∀ x ∈ unitCube d,
      ‖(anchoredSimilarityUnit (ℓ := ℓ) (dyadicNormalizedAnchor j x)).val‖ *
        ‖((anchoredSimilarityUnit (ℓ := ℓ) (dyadicNormalizedAnchor j x))⁻¹).val‖ ≤ χ := by
  obtain ⟨χ, hχ, hQ⟩ := anchoredSimilarityUnit_uniform_condition (d := d) (ℓ := ℓ)
  exact ⟨χ, hχ, fun j x hx => hQ _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx)⟩

end NearlyMinimax
