module

public import NearlyMinimax.UniformInverseDerivatives


@[expose] public section

/-! Uniform derivative bounds for the actual inverse polynomials in similarity charts. -/

noncomputable section
namespace NearlyMinimax
open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixDeterminant

section Similarity
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def complexMatrixSimilarity (Q : (Matrix n n ℂ)ˣ) : Matrix n n ℂ →ₐ[ℝ] Matrix n n ℂ where
  toFun A := (Q : Matrix n n ℂ) * A * (↑Q⁻¹ : Matrix n n ℂ)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by rw [Algebra.algebraMap_eq_smul_one]; simp

theorem complexMatrixSimilarity_norm_le (Q : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    ‖complexMatrixSimilarity Q A‖ ≤ ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ * ‖A‖ := by
  calc
    _ ≤ ‖(Q : Matrix n n ℂ) * A‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ := norm_mul_le _ _
    _ ≤ (‖(Q : Matrix n n ℂ)‖ * ‖A‖) * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

@[simp] theorem complexMatrixSimilarity_inverse (Q : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    complexMatrixSimilarity Q (complexMatrixSimilarity Q⁻¹ A) = A := by
  simp [complexMatrixSimilarity, Matrix.mul_assoc]

theorem normalizeMatrix_similarity (lo hi : ℝ) (Q : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    normalizeMatrix lo hi (complexMatrixSimilarity Q A) =
      complexMatrixSimilarity Q (normalizeMatrix lo hi A) := by
  simp [normalizeMatrix, map_sub, map_smul]

theorem similar_complex_kernel_coefficient_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B : Matrix n n ℂ) (Q : (Matrix n n ℂ)ˣ) (χ : ℝ) (hχ : 0 ≤ χ)
    (hQ : ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ A).IsHermitian)
    (hSpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ A) ⊆ Set.Icc lo hi)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : χ * ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      (4 * χ) * (intervalRho lo hi / η) ^ k := by
  have hd' : ‖normalizeMatrix lo hi (complexMatrixSimilarity Q⁻¹ B) -
      normalizeMatrix lo hi (complexMatrixSimilarity Q⁻¹ A)‖ ≤ δ := by
    rw [normalizeMatrix_similarity, normalizeMatrix_similarity, ← map_sub]
    apply (complexMatrixSimilarity_norm_le Q⁻¹ _).trans
    apply (mul_le_mul_of_nonneg_right _ (norm_nonneg _)).trans hd
    simpa only [inv_inv, mul_comm] using hQ
  have hc := complex_kernel_coefficient_bound lo hi hlo hlt
    (complexMatrixSimilarity Q⁻¹ A) (complexMatrixSimilarity Q⁻¹ B) hA hSpec
    η δ hη hη1 hδ hsmall hd' k
  have he : aeval B (kernelCoefficientPolynomial lo hi k) =
      complexMatrixSimilarity Q (aeval (complexMatrixSimilarity Q⁻¹ B) (kernelCoefficientPolynomial lo hi k)) := by
    rw [← Polynomial.aeval_algHom_apply, complexMatrixSimilarity_inverse]
  rw [he]
  calc
    _ ≤ ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ *
        ‖aeval (complexMatrixSimilarity Q⁻¹ B) (kernelCoefficientPolynomial lo hi k)‖ :=
      complexMatrixSimilarity_norm_le _ _
    _ ≤ χ * (4 * (intervalRho lo hi / η) ^ k) := mul_le_mul hQ hc (norm_nonneg _) hχ
    _ = _ := by ring

end Similarity

section RealCharts
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Real-to-complex matrix extension preserves the genuine operator norm. -/
theorem complexify_matrix_norm (A : Matrix n n ℝ) : ‖A.map Complex.ofReal‖ = ‖A‖ := by
  let φ := ofRealMatrixStarAlgHom (n := n)
  change ‖φ A‖ = ‖A‖
  have hs : IsSelfAdjoint (star A * A) := .star_mul_self A
  have hspec : spectrum ℝ (φ (star A * A)) = spectrum ℝ (star A * A) :=
    complexify_matrix_spectrum (star A * A) (Matrix.isHermitian_iff_isSelfAdjoint.mpr hs)
  have hgR := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (star A * A) hs
  have hgC := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ (star A * A)) (hs.map φ)
  rw [hspec] at hgC
  have he : ‖φ (star A * A)‖ = ‖star A * A‖ := hgC.unique hgR
  have hm : φ (star A * A) = star (φ A) * φ A := by rw [map_mul, map_star]
  rw [hm, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp he

def complexifyMatrixUnit (Q : (Matrix n n ℝ)ˣ) : (Matrix n n ℂ)ˣ :=
  Units.map Complex.ofRealHom.mapMatrix.toMonoidHom Q

@[simp] theorem complexifyMatrixUnit_coe (Q : (Matrix n n ℝ)ˣ) :
    (complexifyMatrixUnit Q : Matrix n n ℂ) = (Q : Matrix n n ℝ).map Complex.ofReal := rfl

@[simp] theorem complexifyMatrixUnit_inv (Q : (Matrix n n ℝ)ˣ) :
    complexifyMatrixUnit Q⁻¹ = (complexifyMatrixUnit Q)⁻¹ := by
  rfl

theorem complexifyMatrixUnit_condition (Q : (Matrix n n ℝ)ˣ) :
    ‖(complexifyMatrixUnit Q : Matrix n n ℂ)‖ * ‖(↑(complexifyMatrixUnit Q)⁻¹ : Matrix n n ℂ)‖ =
      ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ := by
  rw [← complexifyMatrixUnit_inv, complexifyMatrixUnit_coe, complexifyMatrixUnit_coe,
    complexify_matrix_norm, complexify_matrix_norm]

theorem complexify_matrix_similarity (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    complexMatrixSimilarity (complexifyMatrixUnit Q) (A.map Complex.ofReal) =
      (matrixSimilarity Q A).map Complex.ofReal := by
  change _ * _ * _ = ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ)).map Complex.ofReal
  rw [← complexifyMatrixUnit_inv, complexifyMatrixUnit_coe, complexifyMatrixUnit_coe]
  change Complex.ofRealHom.mapMatrix (Q : Matrix n n ℝ) * Complex.ofRealHom.mapMatrix A *
    Complex.ofRealHom.mapMatrix (↑Q⁻¹ : Matrix n n ℝ) =
    Complex.ofRealHom.mapMatrix ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ))
  rw [map_mul, map_mul]

end RealCharts

section Neighborhood
variable (r : ℕ) [NeZero r]

def similarInverseCoordinateRadius (lo hi η χ : ℝ) : ℝ :=
  min 1 ((4 * perturbationConstant η)⁻¹ /
    (χ * max 1 (|(intervalHalfWidth lo hi)⁻¹| *
      (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖))))

theorem similarInverseCoordinateRadius_pos (lo hi η χ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < similarInverseCoordinateRadius r lo hi η χ := by
  have hK := perturbationConstant_pos η hη hη1
  unfold similarInverseCoordinateRadius
  apply lt_min (by norm_num)
  apply div_pos (by positivity)
  apply mul_pos hχ
  exact (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)

theorem coordinate_similar_perturbation (lo hi η χ : ℝ) (hχ : 0 < χ)
    (z z₀ : incrementVariables r → ℂ)
    (hz : ‖z - z₀‖ < similarInverseCoordinateRadius r lo hi η χ)
    (F : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (hF : ‖F‖ ≤ ‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖) :
    χ * ‖normalizeMatrix lo hi (F z) - normalizeMatrix lo hi (F z₀)‖ ≤
      (4 * perturbationConstant η)⁻¹ := by
  let D := max 1 (|(intervalHalfWidth lo hi)⁻¹| *
    (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖))
  have hD : 0 < D := (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have hz' : ‖z - z₀‖ ≤ (4 * perturbationConstant η)⁻¹ / (χ * D) :=
    hz.le.trans (min_le_right _ _)
  rw [normalizeMatrix_sub, norm_smul, Real.norm_eq_abs, ← map_sub]
  calc
    _ ≤ χ * (|(intervalHalfWidth lo hi)⁻¹| * (‖F‖ * ‖z - z₀‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (F.le_opNorm _) (abs_nonneg _)) hχ.le
    _ ≤ (χ * D) * ‖z - z₀‖ := by
      have hc : |(intervalHalfWidth lo hi)⁻¹| * ‖F‖ ≤ D :=
        (mul_le_mul_of_nonneg_left hF (abs_nonneg _)).trans (le_max_right _ _)
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hχ.le (norm_nonneg (z - z₀)))
      nlinarith only [hh]
    _ ≤ _ := by simpa only [mul_comm] using (le_div_iff₀ (mul_pos hχ hD)).mp hz'

def similarInverseEnvelope (lo hi q χ : ℝ) : ℝ :=
  |(intervalGeometricMean lo hi ^ (r + 1))⁻¹| *
    ((Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ (r + 1)) *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ k

def boundedNumeratorEnvelope (L Y : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ∑ j : Fin r, (
    polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
      Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1))

def similarIncrementEnvelope (lo hi q χ L Y : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  similarInverseEnvelope r lo hi q χ * boundedNumeratorEnvelope r L Y T

theorem similarInverseEnvelope_nonneg (lo hi q χ : ℝ) (hq : 0 ≤ q) (hχ : 0 ≤ χ) :
    0 ≤ similarInverseEnvelope r lo hi q χ := by
  unfold similarInverseEnvelope
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (fun k => by positivity)

theorem bounded_numerator_complex_bound (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (z : incrementVariables r → ℂ) (hz : ∀ j, ‖z j‖ ≤ L + 1) (i : Fin r) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y i)‖ ≤
      polynomialCoordinateBound (rawNumeratorPolynomial r T false i) (L + 1) +
        Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true i) (L + 1) := by
  simp only [numeratorPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  calc
    _ ≤ ‖MvPolynomial.eval₂ Complex.ofRealHom z (rawNumeratorPolynomial r T false i)‖ +
        ‖Complex.ofRealHom y * MvPolynomial.eval₂ Complex.ofRealHom z (rawNumeratorPolynomial r T true i)‖ :=
      norm_sub_le _ _
    _ ≤ _ := by
      apply add_le_add (polynomial_complex_coordinate_bound _ z _ (by positivity) hz)
      rw [norm_mul]
      change ‖(y : ℂ)‖ * _ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hy (polynomial_complex_coordinate_bound _ z _ (by positivity) hz)
        (norm_nonneg _) hY

theorem actual_similar_increment_complex_neighborhood (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (z₀ z : incrementVariables r → ℂ) (hz₀ : ‖z₀‖ ≤ L)
    (Q S : (Matrix (Fin r) (Fin r) ℂ)ˣ)
    (hQ : ‖(Q : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hS : ‖(S : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑S⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r z₀)).IsHermitian)
    (hC : (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r z₀)).IsHermitian)
    (hASpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r z₀)) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r z₀)) ⊆ Set.Icc lo hi)
    (hz : ‖z - z₀‖ < similarInverseCoordinateRadius r lo hi η χ) (m : ℕ) (i : Fin r) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z (incrementEntryPolynomial r lo hi T y m i)‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T := by
  have hρ := intervalRho_pos lo hi hlo hlt
  have hη : 0 < η := hρ.trans hρη
  have hq : 0 < intervalRho lo hi / η := div_pos hρ hη
  have hq1 : intervalRho lo hi / η < 1 := (div_lt_one hη).mpr hρη
  have hδ : 0 ≤ (4 * perturbationConstant η)⁻¹ :=
    (inv_pos.mpr (mul_pos (by norm_num) (perturbationConstant_pos η hη hη1))).le
  have hsmall : 4 * (4 * perturbationConstant η)⁻¹ * perturbationConstant η ≤ 1 := by
    have hK := ne_of_gt (perturbationConstant_pos η hη hη1)
    field_simp
    norm_num
  have hdA := coordinate_similar_perturbation r lo hi η χ hχ z z₀ hz
    (currentCoordinateCLM r) (le_add_of_nonneg_right (norm_nonneg _))
  have hdC := coordinate_similar_perturbation r lo hi η χ hχ z z₀ hz
    (parentCoordinateCLM r) (le_add_of_nonneg_left (norm_nonneg _))
  have hK (a b : Fin r) (k : ℕ) :
      ‖PowerSeries.coeff k (complexKernelSeries lo hi (currentCoordinateCLM r z) a b)‖ ≤
        (4 * χ) * (intervalRho lo hi / η) ^ k := by
    simp only [complexKernelSeries, PowerSeries.coeff_mk]
    exact (matrix_entry_norm_le_l2 _ a b).trans
      (similar_complex_kernel_coefficient_bound lo hi hlo hlt _ _ Q χ hχ.le hQ hA hASpec
        η _ hη hη1 hδ hsmall hdA k)
  have hD (a b : Fin r) (k : ℕ) :
      ‖PowerSeries.coeff k (complexKernelSeries lo hi (parentCoordinateCLM r z) a b)‖ ≤
        (4 * χ) * (intervalRho lo hi / η) ^ k := by
    simp only [complexKernelSeries, PowerSeries.coeff_mk]
    exact (matrix_entry_norm_le_l2 _ a b).trans
      (similar_complex_kernel_coefficient_bound lo hi hlo hlt _ _ S χ hχ.le hS hC hCSpec
        η _ hη hη1 hδ hsmall hdC k)
  have hzR : ∀ j, ‖z j‖ ≤ L + 1 := by
    intro j
    apply (norm_le_pi_norm z j).trans
    calc
      ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + L := add_le_add (hz.le.trans (min_le_left _ _)) hz₀
      _ = _ := by ring
  have hI (j : Fin r) :
      ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j))‖ ≤
        similarInverseEnvelope r lo hi (intervalRho lo hi / η) χ := by
    rw [MvPolynomial.eval₂_rename, coordinate_parent_valuation,
      parentInverseEntryPolynomial_eval_complex, norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left
      (combined_truncation_uniform_bound _ _ _ (4 * χ) hq hq1 (by positivity) hK hD i j m)
      (abs_nonneg _)).trans_eq (by simp [similarInverseEnvelope, mul_assoc])
  simp only [incrementEntryPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul]
  calc
    _ ≤ ∑ j : Fin r, ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j)) *
        MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin r, similarInverseEnvelope r lo hi (intervalRho lo hi / η) χ *
        (polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
          Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hI j) (bounded_numerator_complex_bound r L Y hL hY T y hy z hzR j)
        (norm_nonneg _) (similarInverseEnvelope_nonneg r lo hi _ χ hq.le hχ.le)
    _ = _ := by rw [← Finset.mul_sum]; rfl

end Neighborhood

section Derivatives
open RoughRegime.ComplexDerivativeBridge
variable (r : ℕ) [NeZero r]

private theorem norm_reindex_le {V W : Type*} [Fintype V] [Fintype W]
    (z : V → ℂ) (f : W → V) : ‖z ∘ f‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro j
  exact norm_le_pi_norm z (f j)

/-- All positive-order real derivatives of the actual free-moment increment obey a
single factorial bound, uniformly in truncation degree, bounded response, and center. -/
theorem actual_similar_increment_derivative_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (u : incrementVariables r → ℝ) (hu : ‖u‖ ≤ L)
    (Q S : (Matrix (Fin r) (Fin r) ℂ)ˣ)
    (hQ : ‖(Q : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hS : ‖(S : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑S⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (u j : ℂ)))).IsHermitian)
    (hC : (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (u j : ℂ)))).IsHermitian)
    (hASpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (u j : ℂ)))) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (u j : ℂ)))) ⊆ Set.Icc lo hi)
    (m k : ℕ) (hk : 0 < k) (i : Fin r)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => u ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * (k.factorial : ℝ) *
        (Real.exp 1 / similarInverseCoordinateRadius r lo hi η χ) ^ k * ∏ j, ‖v j‖ := by
  have hη : 0 < η := (intervalRho_pos lo hi hlo hlt).trans hρη
  let uFin := fun j => u ((Fintype.equivFin (incrementVariables r)).symm j)
  let z₀ : incrementVariables r → ℂ := fun j => (u j : ℂ)
  have hz₀ : ‖z₀‖ ≤ L := by
    apply (pi_norm_le_iff_of_nonneg hL).mpr
    intro j
    have hj : ‖z₀ j‖ ≤ ‖u‖ := by simpa [z₀] using norm_le_pi_norm u j
    exact hj.trans hu
  apply real_polynomial_derivative_bound _ uFin _ _
    (similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ) _ hk v
  intro z hz
  rw [complexify, MvPolynomial.eval_map, incrementFinPolynomial, MvPolynomial.eval₂_rename]
  apply actual_similar_increment_complex_neighborhood r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy
    z₀ (z ∘ Fintype.equivFin (incrementVariables r)) hz₀ Q S hQ hS hA hC hASpec hCSpec _ m i
  have he : z ∘ Fintype.equivFin (incrementVariables r) - z₀ =
      (z - (fun j => (uFin j : ℂ))) ∘ Fintype.equivFin (incrementVariables r) := by
    funext j
    simp [z₀, uFin]
  rw [he]
  exact (norm_reindex_le _ _).trans_lt hz

/-- The zeroth-order endpoint uses the same envelope as every derivative order. -/
theorem actual_similar_increment_order_zero_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (u : incrementVariables r → ℝ) (hu : ‖u‖ ≤ L)
    (Q S : (Matrix (Fin r) (Fin r) ℂ)ˣ)
    (hQ : ‖(Q : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hS : ‖(S : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑S⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (u j : ℂ)))).IsHermitian)
    (hC : (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (u j : ℂ)))).IsHermitian)
    (hASpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (u j : ℂ)))) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (u j : ℂ)))) ⊆ Set.Icc lo hi)
    (m : ℕ) (i : Fin r) :
    ‖MvPolynomial.eval u (incrementEntryPolynomial r lo hi T y m i)‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T := by
  have hη : 0 < η := (intervalRho_pos lo hi hlo hlt).trans hρη
  have hz : ‖(fun j => (u j : ℂ))‖ ≤ L := by
    apply (pi_norm_le_iff_of_nonneg hL).mpr
    intro j
    have hj : ‖(u j : ℂ)‖ ≤ ‖u‖ := by simpa using norm_le_pi_norm u j
    exact hj.trans hu
  have hc := actual_similar_increment_complex_neighborhood r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy
    (fun j => (u j : ℂ)) (fun j => (u j : ℂ)) hz Q S hQ hS hA hC hASpec hCSpec
    (by simpa using similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ) m i
  have he : MvPolynomial.eval₂ Complex.ofRealHom (fun j => (u j : ℂ))
      (incrementEntryPolynomial r lo hi T y m i) =
      (MvPolynomial.eval u (incrementEntryPolynomial r lo hi T y m i) : ℂ) :=
    (MvPolynomial.eval₂_comp Complex.ofRealHom u _).symm
  rw [he, Complex.norm_real] at hc
  exact hc

end Derivatives

section PaperEndpoint
variable (r : ℕ) [NeZero r]

/-- Primitive center conditions: real free moments, a fixed bound, and the two
real similarity charts with the manuscript's common spectral interval. -/
structure InverseDerivativeCenter (lo hi χ L : ℝ) where
  moments : incrementVariables r → ℝ
  normBound : ‖moments‖ ≤ L
  currentChart : (Matrix (Fin r) (Fin r) ℝ)ˣ
  parentChart : (Matrix (Fin r) (Fin r) ℝ)ˣ
  currentCondition : ‖(currentChart : Matrix (Fin r) (Fin r) ℝ)‖ *
    ‖(↑currentChart⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ
  parentCondition : ‖(parentChart : Matrix (Fin r) (Fin r) ℝ)‖ *
    ‖(↑parentChart⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ
  currentHermitian : (matrixSimilarity currentChart⁻¹ (currentRealCoordinateMatrix r moments)).IsHermitian
  parentHermitian : (matrixSimilarity parentChart⁻¹ (parentRealCoordinateMatrix r moments)).IsHermitian
  currentSpectrum : spectrum ℝ (matrixSimilarity currentChart⁻¹ (currentRealCoordinateMatrix r moments)) ⊆ Set.Icc lo hi
  parentSpectrum : spectrum ℝ (matrixSimilarity parentChart⁻¹ (parentRealCoordinateMatrix r moments)) ⊆ Set.Icc lo hi

def inverseDerivativeRate (lo hi η χ : ℝ) : ℝ :=
  Real.exp 1 / similarInverseCoordinateRadius r lo hi η χ

theorem inverseDerivativeRate_pos (lo hi η χ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < inverseDerivativeRate r lo hi η χ :=
  div_pos (Real.exp_pos _) (similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ)

theorem similarIncrementEnvelope_nonneg (lo hi q χ L Y : ℝ)
    (hq : 0 ≤ q) (hχ : 0 ≤ χ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) : 0 ≤ similarIncrementEnvelope r lo hi q χ L Y T := by
  unfold similarIncrementEnvelope boundedNumeratorEnvelope
  apply mul_nonneg (similarInverseEnvelope_nonneg r lo hi q χ hq hχ)
  exact Finset.sum_nonneg (fun j hj => add_nonneg
    (polynomialCoordinateBound_nonneg _ _ (by positivity))
    (mul_nonneg hY (polynomialCoordinateBound_nonneg _ _ (by positivity))))

/-- The complete U5 analytic input: every order, the actual complexified polynomials,
and constants independent of truncation degree and the admissible center. -/
theorem paper_inverse_derivative_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter r lo hi χ L) (m k : ℕ) (i : Fin r)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * (k.factorial : ℝ) *
        inverseDerivativeRate r lo hi η χ ^ k * ∏ j, ‖v j‖ := by
  let Q := complexifyMatrixUnit c.currentChart
  let S := complexifyMatrixUnit c.parentChart
  have hQ : ‖(Q : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ := by
    rw [complexifyMatrixUnit_condition]
    exact c.currentCondition
  have hS : ‖(S : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑S⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ := by
    rw [complexifyMatrixUnit_condition]
    exact c.parentCondition
  have hAeq : complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (c.moments j : ℂ))) =
      (matrixSimilarity c.currentChart⁻¹ (currentRealCoordinateMatrix r c.moments)).map Complex.ofReal := by
    change complexMatrixSimilarity (complexifyMatrixUnit c.currentChart)⁻¹
      ((currentRealCoordinateMatrix r c.moments).map Complex.ofReal) = _
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity]
  have hCeq : complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (c.moments j : ℂ))) =
      (matrixSimilarity c.parentChart⁻¹ (parentRealCoordinateMatrix r c.moments)).map Complex.ofReal := by
    change complexMatrixSimilarity (complexifyMatrixUnit c.parentChart)⁻¹
      ((parentRealCoordinateMatrix r c.moments).map Complex.ofReal) = _
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity]
  have hA : (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (c.moments j : ℂ)))).IsHermitian := by
    rw [hAeq]
    exact c.currentHermitian.map _ (fun x => by simp)
  have hC : (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (c.moments j : ℂ)))).IsHermitian := by
    rw [hCeq]
    exact c.parentHermitian.map _ (fun x => by simp)
  have hASpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (c.moments j : ℂ)))) ⊆ Set.Icc lo hi := by
    rw [hAeq, complexify_matrix_spectrum _ c.currentHermitian]
    exact c.currentSpectrum
  have hCSpec : spectrum ℝ (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (c.moments j : ℂ)))) ⊆ Set.Icc lo hi := by
    rw [hCeq, complexify_matrix_spectrum _ c.parentHermitian]
    exact c.parentSpectrum
  cases k with
  | zero =>
    simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
      Fin.prod_univ_zero, incrementFinPolynomial, MvPolynomial.eval_rename]
    have he : (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) ∘
      Fintype.equivFin (incrementVariables r) = c.moments := by funext j; simp
    rw [he]
    exact actual_similar_increment_order_zero_bound r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY
      T y hy c.moments c.normBound Q S hQ hS hA hC hASpec hCSpec m i
  | succ k =>
    exact actual_similar_increment_derivative_bound r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY
      T y hy c.moments c.normBound Q S hQ hS hA hC hASpec hCSpec m (k + 1) (by omega) i v

def incrementFinVector (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  fun x i => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i)

theorem incrementFinVector_contDiff (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) :
    ContDiff ℝ ⊤ (incrementFinVector r lo hi T y m) :=
  contDiff_pi.mpr (fun i => RoughRegime.PolynomialDerivatives.polynomial_contDiff _)

/-- Vector-valued derivative endpoint in the fixed finite-coordinate norm. -/
theorem paper_inverse_vector_derivative_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ : ℝ) (hχ : 0 < χ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter r lo hi χ L) (m k : ℕ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m)
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * (k.factorial : ℝ) *
        inverseDerivativeRate r lo hi η χ ^ k * ∏ j, ‖v j‖ := by
  have hη : 0 < η := (intervalRho_pos lo hi hlo hlt).trans hρη
  have hM := similarIncrementEnvelope_nonneg r lo hi _ χ L Y
    (div_pos (intervalRho_pos lo hi hlo hlt) hη).le hχ.le hL hY T
  have hRate := inverseDerivativeRate_pos r lo hi η χ hη hη1 hχ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hd := (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (x := fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j))
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have he := congrArg (fun D => D v) hd
  change iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v =
    (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m)
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v) i at he
  rw [← he]
  exact paper_inverse_derivative_bound r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy c m k i v

end PaperEndpoint
end NearlyMinimax
