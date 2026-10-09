module

public import NearlyMinimax.AnchoredGramBounds


@[expose] public section

/-! Genuine whitening and spectral localization of the population anchored Gram. -/

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace NearlyMinimax

/-- The inverse positive square root of the known Lebesgue Gram. -/
def anchoredWhitening {d ℓ : ℕ} (u : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (CFC.sqrt (anchoredGram u))⁻¹

theorem anchoredGram_sqrt_isUnit {d ℓ : ℕ} (u : Covariate d) :
    IsUnit (CFC.sqrt (anchoredGram (ℓ := ℓ) u)) :=
  (CFC.isUnit_sqrt_iff _ (anchoredGram_posDef u).posSemidef.nonneg).mpr
    (anchoredGram_posDef u).isUnit

theorem anchoredWhitening_isHermitian {d ℓ : ℕ} (u : Covariate d) :
    (anchoredWhitening (ℓ := ℓ) u).IsHermitian :=
  (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg (anchoredGram u))).isHermitian.inv

theorem anchoredWhitening_gram_identity {d ℓ : ℕ} (u : Covariate d) :
    anchoredWhitening (ℓ := ℓ) u * anchoredGram u * anchoredWhitening u = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  calc
    _ = anchoredWhitening u *
        (CFC.sqrt (anchoredGram u) * CFC.sqrt (anchoredGram u)) * anchoredWhitening u :=
      congrArg (fun M => anchoredWhitening u * M * anchoredWhitening u)
        (CFC.sqrt_mul_sqrt_self (anchoredGram u) (anchoredGram_posDef u).posSemidef.nonneg).symm
    _ = 1 := by
      unfold anchoredWhitening
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul,
        Matrix.mul_nonsing_inv _ hdet]

/-- The symmetric whitened population matrix used in the inverse approximation. -/
def anchoredWhitenedGram {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  anchoredWhitening u * anchoredDensityGram u p * anchoredWhitening u

theorem anchoredWhitenedGram_isHermitian {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) : (anchoredWhitenedGram (ℓ := ℓ) u p).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul (anchoredWhitening (ℓ := ℓ) u)
    (anchoredDensityGram_isHermitian u p)
  rw [(anchoredWhitening_isHermitian u).eq] at h
  exact h

/-- Whitening converts the proved density Gram sandwich into scalar-matrix bounds. -/
theorem anchoredWhitenedGram_sandwich {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    a • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) ≤ anchoredWhitenedGram u p ∧
      anchoredWhitenedGram u p ≤ b • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) := by
  have h := anchoredDensityGram_sandwich (ℓ := ℓ) u p hpmeas a b ha hp
  constructor
  · have hlo := h.1.conjTranspose_mul_mul_same (anchoredWhitening u)
    rw [(anchoredWhitening_isHermitian u).eq] at hlo
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      anchoredWhitening_gram_identity] at hlo
    exact hlo
  · have hup := h.2.conjTranspose_mul_mul_same (anchoredWhitening u)
    rw [(anchoredWhitening_isHermitian u).eq] at hup
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      anchoredWhitening_gram_identity] at hup
    exact hup

/-- The actual normalized population Gram has spectrum in the density interval. -/
theorem anchoredWhitenedGram_spectrum {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    spectrum ℝ (anchoredWhitenedGram (ℓ := ℓ) u p) ⊆ Set.Icc a b := by
  have hs := anchoredWhitenedGram_sandwich (ℓ := ℓ) u p hpmeas a b ha hp
  have hlo : algebraMap ℝ (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) a ≤
      anchoredWhitenedGram u p := by simpa only [Algebra.algebraMap_eq_smul_one] using hs.1
  have hup : anchoredWhitenedGram u p ≤
      algebraMap ℝ (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) b := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hs.2
  intro t ht
  exact ⟨(algebraMap_le_iff_le_spectrum (anchoredWhitenedGram_isHermitian u p)).mp hlo t ht,
    (le_algebraMap_iff_spectrum_le (anchoredWhitenedGram_isHermitian u p)).mp hup t ht⟩

/-- A genuine matrix unit implementing the population similarity transform. -/
def anchoredSimilarityUnit {d ℓ : ℕ} (u : Covariate d) :
    (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ)ˣ :=
  (anchoredGram_sqrt_isUnit (ℓ := ℓ) u).unit⁻¹

@[simp] theorem anchoredSimilarityUnit_val {d ℓ : ℕ} (u : Covariate d) :
    (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitening u := by
  rw [anchoredSimilarityUnit, Matrix.coe_units_inv, IsUnit.unit_spec]
  rfl

@[simp] theorem anchoredSimilarityUnit_inv_val {d ℓ : ℕ} (u : Covariate d) :
    ((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val = CFC.sqrt (anchoredGram u) := by
  simp only [anchoredSimilarityUnit, inv_inv, IsUnit.unit_spec]

theorem anchoredWhitening_square {d ℓ : ℕ} (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u)⁻¹ = anchoredWhitening u * anchoredWhitening u := by
  calc
    (anchoredGram u)⁻¹ = (CFC.sqrt (anchoredGram u) * CFC.sqrt (anchoredGram u))⁻¹ :=
      congrArg Inv.inv (CFC.sqrt_mul_sqrt_self (anchoredGram u)
        (anchoredGram_posDef u).posSemidef.nonneg).symm
    _ = _ := Matrix.mul_inv_rev _ _

/-- The actual preconditioned Gram is similar to the Hermitian spectral matrix. -/
theorem anchored_preconditioned_similarity {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) :
    ((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val *
      ((anchoredGram u)⁻¹ * anchoredDensityGram u p) *
      (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitenedGram u p := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  have hsq := anchoredWhitening_square (ℓ := ℓ) u
  rw [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val, hsq]
  simp only [← Matrix.mul_assoc, anchoredWhitenedGram]
  rw [show CFC.sqrt (anchoredGram u) * anchoredWhitening u = 1 by
    exact Matrix.mul_nonsing_inv _ hdet, one_mul]

theorem anchoredGram_continuous {d ℓ : ℕ} :
    Continuous (anchoredGram (d := d) (ℓ := ℓ)) :=
  continuous_matrix anchoredGram_entry_continuous

theorem anchoredGram_sqrt_continuous {d ℓ : ℕ} :
    Continuous (fun u : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) u)) := by
  exact CFC.continuousOn_sqrt.comp_continuous anchoredGram_continuous
    (fun u => (anchoredGram_posDef u).posSemidef.nonneg)

theorem anchoredWhitening_continuous {d ℓ : ℕ} :
    Continuous (anchoredWhitening (d := d) (ℓ := ℓ)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  have hinv : ContinuousAt Ring.inverse (CFC.sqrt (anchoredGram (ℓ := ℓ) u)).det := by
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [heq]
    exact continuousAt_inv₀ hdet.ne_zero
  have hR : Continuous (fun v : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) v)) :=
    anchoredGram_sqrt_continuous
  have hI : ContinuousAt
      (Inv.inv : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ → Matrix _ _ ℝ)
      (CFC.sqrt (anchoredGram (ℓ := ℓ) u)) := continuousAt_matrix_inv _ hinv
  exact hI.comp (f := fun v : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) v))
    (x := u) (hR.continuousAt (x := u))

/-- A fixed finite condition-number bound exists for every actual similarity
unit, uniformly over anchors. It depends only on the monomial dimensions. -/
theorem anchoredSimilarityUnit_uniform_condition {d ℓ : ℕ} :
    ∃ χ : ℝ, 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖(anchoredSimilarityUnit (ℓ := ℓ) u).val‖ *
        ‖((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ := by
  have hc : Continuous (fun u : Covariate d =>
      ‖anchoredWhitening (ℓ := ℓ) u‖ * ‖CFC.sqrt (anchoredGram (ℓ := ℓ) u)‖) :=
    (anchoredWhitening_continuous (d := d) (ℓ := ℓ)).norm.mul
      (anchoredGram_sqrt_continuous (d := d) (ℓ := ℓ)).norm
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  rw [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val]
  exact (hM (Set.mem_image_of_mem _ hu)).trans (le_max_right _ _)

end NearlyMinimax
