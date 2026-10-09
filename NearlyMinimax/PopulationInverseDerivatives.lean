module

public import NearlyMinimax.SimilarInverseDerivatives
public import NearlyMinimax.AnchoredSpectrum


@[expose] public section

/-! Concrete population matrix charts feeding the degree-independent inverse bounds. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

section Reindex
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    [Nonempty n] [Nonempty m]

/-- Canonical matrix reindexing preserves the operator norm. -/
theorem reindex_matrix_norm (e : n ≃ m) (A : Matrix n n ℝ) : ‖A.reindex e e‖ = ‖A‖ := by
  let φ := Matrix.reindexAlgEquiv ℝ ℝ e
  change ‖φ A‖ = ‖A‖
  have hs : IsSelfAdjoint (star A * A) := .star_mul_self A
  have hs' : IsSelfAdjoint (φ (star A * A)) := Matrix.isHermitian_iff_isSelfAdjoint.mp
    ((Matrix.isHermitian_iff_isSelfAdjoint.mpr hs).reindex e)
  have hspec : spectrum ℝ (φ (star A * A)) = spectrum ℝ (star A * A) := AlgEquiv.spectrum_eq φ _
  have hgR := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (star A * A) hs
  have hgS := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ (star A * A)) hs'
  rw [hspec] at hgS
  have he : ‖φ (star A * A)‖ = ‖star A * A‖ := hgS.unique hgR
  have hm : φ (star A * A) = star (φ A) * φ A := by
    rw [map_mul]
    rfl
  rw [hm, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp he

end Reindex

abbrev anchoredDimension (d ℓ : ℕ) := Fintype.card (AnchoredIndex d ℓ)

instance anchoredDimension_neZero {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)] :
    NeZero (anchoredDimension d ℓ) := ⟨Fintype.card_ne_zero⟩

def anchoredFinReindex (d ℓ : ℕ) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ ≃ₐ[ℝ]
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (Fintype.equivFin (AnchoredIndex d ℓ))

def anchoredFinNormalizedGram {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ ((anchoredGram u)⁻¹ * anchoredDensityGram u p)

def anchoredFinSimilarityUnit {d ℓ : ℕ} (u : Covariate d) :
    (Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ)ˣ :=
  Units.map (anchoredFinReindex d ℓ).toMonoidHom (anchoredSimilarityUnit u)

@[simp] theorem anchoredFinSimilarityUnit_val {d ℓ : ℕ} (u : Covariate d) :
    (anchoredFinSimilarityUnit (ℓ := ℓ) u).val = anchoredFinReindex d ℓ (anchoredSimilarityUnit u).val := rfl

@[simp] theorem anchoredFinSimilarityUnit_inv_val {d ℓ : ℕ} (u : Covariate d) :
    ((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val =
      anchoredFinReindex d ℓ ((anchoredSimilarityUnit u)⁻¹).val := rfl

theorem anchoredFin_similarity {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p) =
      anchoredFinReindex d ℓ (anchoredWhitenedGram u p) := by
  change anchoredFinReindex d ℓ _ * anchoredFinReindex d ℓ _ * anchoredFinReindex d ℓ _ = _
  rw [← map_mul, ← map_mul]
  exact congrArg (anchoredFinReindex d ℓ) (anchored_preconditioned_similarity u p)

theorem anchoredFin_similarity_isHermitian {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    (matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p)).IsHermitian := by
  rw [anchoredFin_similarity]
  exact (anchoredWhitenedGram_isHermitian u p).reindex (Fintype.equivFin (AnchoredIndex d ℓ))

theorem anchoredFin_similarity_spectrum {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    spectrum ℝ (matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p)) ⊆ Set.Icc a b := by
  rw [anchoredFin_similarity, AlgEquiv.spectrum_eq]
  exact anchoredWhitenedGram_spectrum u p hpmeas a b ha hp

theorem anchoredFinSimilarityUnit_uniform_condition {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)] :
    ∃ χ : ℝ, 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
        ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ := by
  obtain ⟨χ, hχ, hQ⟩ := anchoredSimilarityUnit_uniform_condition (d := d) (ℓ := ℓ)
  refine ⟨χ, hχ, ?_⟩
  intro u hu
  rw [anchoredFinSimilarityUnit_val, anchoredFinSimilarityUnit_inv_val]
  change ‖((anchoredSimilarityUnit u).val).reindex _ _‖ *
    ‖(((anchoredSimilarityUnit u)⁻¹).val).reindex _ _‖ ≤ χ
  rw [reindex_matrix_norm, reindex_matrix_norm]
  exact hQ u hu

theorem positive_spectral_matrix_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : ‖A‖ ≤ b := by
  have hs : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  rw [← cfc_id ℝ A hs]
  apply norm_cfc_le hb
  intro t ht
  rw [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.trans (hSpec ht).1)]
  exact (hSpec ht).2

theorem anchoredFinNormalizedGram_norm_le {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (u : Covariate d) (p : Covariate d → ℝ) (hpmeas : Measurable p)
    (a b χ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hχ : 0 ≤ χ)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hQ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
      ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ) :
    ‖anchoredFinNormalizedGram (ℓ := ℓ) u p‖ ≤ χ * b := by
  let Q := anchoredFinSimilarityUnit (ℓ := ℓ) u
  let A := anchoredFinNormalizedGram (ℓ := ℓ) u p
  have he : matrixSimilarity Q (matrixSimilarity Q⁻¹ A) = A := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  change ‖A‖ ≤ χ * b
  rw [← he]
  apply (matrixSimilarity_norm_le Q _).trans
  exact mul_le_mul hQ
    (positive_spectral_matrix_norm_le _ (anchoredFin_similarity_isHermitian u p) a b ha hb
      (anchoredFin_similarity_spectrum u p hpmeas a b ha hp)) (norm_nonneg _) hχ

theorem matrix_real_entry_norm_le {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  rw [← complexify_matrix_norm A, ← Complex.norm_real (A i j)]
  exact matrix_entry_norm_le_l2 (A.map Complex.ofReal) i j

theorem incrementValuation_norm_le {r : ℕ} [NeZero r]
    (A C : Matrix (Fin r) (Fin r) ℝ) (U V : Bool → Fin r → ℝ)
    (M W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hA : ‖A‖ ≤ M) (hC : ‖C‖ ≤ M) (hU : ∀ t, ‖U t‖ ≤ W) (hV : ∀ t, ‖V t‖ ≤ W) :
    ‖incrementValuation A C U V‖ ≤ max M W := by
  apply (pi_norm_le_iff_of_nonneg (hM.trans (le_max_left _ _))).mpr
  intro z
  cases z with
  | inl z =>
    cases z with
    | inl ij => exact ((matrix_real_entry_norm_le A ij.1 ij.2).trans hA).trans (le_max_left _ _)
    | inr z => exact ((matrix_real_entry_norm_le C z.2.1 z.2.2).trans hC).trans (le_max_left _ _)
  | inr z =>
    rcases z with ⟨parent, response, i⟩
    cases parent with
    | false => exact ((norm_le_pi_norm (U response) i).trans (hU response)).trans (le_max_right _ _)
    | true => exact ((norm_le_pi_norm (V response) i).trans (hV response)).trans (le_max_right _ _)

/-- The population center is constructed from actual normalized density Grams.
Only the four vector-moment bounds remain as explicit input to this constructor. -/
def populationInverseDerivativeCenter {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (u v : Covariate d) (p q : Covariate d → ℝ) (hpmeas : Measurable p) (hqmeas : Measurable q)
    (a b χ W : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hχ : 0 ≤ χ) (hW : 0 ≤ W)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hq : ∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b)
    (hUQ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ * ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ)
    (hVQ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) v).val‖ * ‖((anchoredFinSimilarityUnit (ℓ := ℓ) v)⁻¹).val‖ ≤ χ)
    (U V : Bool → Fin (anchoredDimension d ℓ) → ℝ)
    (hU : ∀ t, ‖U t‖ ≤ W) (hV : ∀ t, ‖V t‖ ≤ W) :
    InverseDerivativeCenter (anchoredDimension d ℓ) a b χ (max (χ * b) W) where
  moments := incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
  normBound := incrementValuation_norm_le _ _ U V _ W (mul_nonneg hχ hb) hW
    (anchoredFinNormalizedGram_norm_le u p hpmeas a b χ ha hb hχ hp hUQ)
    (anchoredFinNormalizedGram_norm_le v q hqmeas a b χ ha hb hχ hq hVQ) hU hV
  currentChart := anchoredFinSimilarityUnit u
  parentChart := anchoredFinSimilarityUnit v
  currentCondition := hUQ
  parentCondition := hVQ
  currentHermitian := anchoredFin_similarity_isHermitian u p
  parentHermitian := anchoredFin_similarity_isHermitian v q
  currentSpectrum := anchoredFin_similarity_spectrum u p hpmeas a b ha hp
  parentSpectrum := anchoredFin_similarity_spectrum v q hqmeas a b ha hq

def anchoredFinTransport (d ℓ : ℕ) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ (anchoredTransport d ℓ)

/-- The actual anchored population matrices obey the common derivative bound.
No chart, spectrum, or condition bound is supplied by the caller. -/
theorem anchored_population_inverse_derivatives {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (a b W Y : ℝ) (ha : 0 < a) (hab : a < b) (hW : 0 ≤ W) (hY : 0 ≤ Y) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (u v : Covariate d), u ∈ unitCube d → v ∈ unitCube d →
      ∀ (p q : Covariate d → ℝ), Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      ∀ (U V : Bool → Fin (anchoredDimension d ℓ) → ℝ),
      (∀ t, ‖U t‖ ≤ W) → (∀ t, ‖V t‖ ≤ W) →
      ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ directions : Fin k → Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ,
        ‖iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ ≤
            C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖ := by
  obtain ⟨χ, hχ, hQ⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := ℓ)
  let η := (1 + RoughRegime.Upper.intervalRho a b) / 2
  have hρ := RoughRegime.Upper.intervalRho_pos a b ha hab
  have hρ1 := RoughRegime.Upper.intervalRho_lt_one a b ha hab
  have hρη : RoughRegime.Upper.intervalRho a b < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  have hη : 0 < η := hρ.trans hρη
  let L := max (χ * b) W
  have hb : 0 < b := ha.trans hab
  have hL : 0 ≤ L := (mul_nonneg hχ.le hb.le).trans (le_max_left _ _)
  let M := similarIncrementEnvelope (anchoredDimension d ℓ) a b
    (RoughRegime.Upper.intervalRho a b / η) χ L Y (anchoredFinTransport d ℓ)
  refine ⟨max 1 M, inverseDerivativeRate (anchoredDimension d ℓ) a b η χ,
    (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _),
    inverseDerivativeRate_pos _ a b η χ hη hη1 hχ, ?_⟩
  intro u v hu hv p q hpmeas hqmeas hp hq U V hU hV y hy m k directions
  let c : InverseDerivativeCenter (anchoredDimension d ℓ) a b χ L :=
    populationInverseDerivativeCenter (ℓ := ℓ) u v p q hpmeas hqmeas a b χ W ha.le hb.le hχ.le hW
    hp hq (hQ u hu) (hQ v hv) U V hU hV
  have h := paper_inverse_vector_derivative_bound (anchoredDimension d ℓ) a b ha hab η hρη hη1 χ hχ
    L Y hL hY (anchoredFinTransport d ℓ) y hy c m k directions
  have hRate := inverseDerivativeRate_pos (anchoredDimension d ℓ) a b η χ hη hη1 hχ
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun j _ => norm_nonneg (directions j)))
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hRate.le k)
  exact mul_le_mul_of_nonneg_right (le_max_right 1 M) (Nat.cast_nonneg _)

end NearlyMinimax
