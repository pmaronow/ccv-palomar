module

public import NearlyMinimax.HighSpatialEnvelopes


@[expose] public section

/-! Genuine pure heat numerator when a target row is omitted. The envelope
is constant in the chart and needs only legal response masses. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def highHeatRawNumerator {ι : Type*} [Fintype ι] {n : ℕ} (a V η : ℝ)
    (p g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  -(η^2*(∏ i, p i)*∑ i, (w i)^2*highResponseVarianceTerm a V η g w φ c y i)

 def highHeatGeometryEnvelope (n : ℕ) (bd a η : ℝ) : ℝ :=
  (3 : ℝ)^n*(η^2*bd^n*(n : ℝ)/a^2)^2

 def highHeatSpatialBudget (d n : ℕ) (bd a η : ℝ) : ℝ :=
  (η^2*bd^n*(n : ℝ)/a^2)^2*(2 : ℝ)^(d*n)

 theorem highHeatGeometryEnvelope_nonneg (n : ℕ) (bd a η : ℝ) :
    0 ≤ highHeatGeometryEnvelope n bd a η := by unfold highHeatGeometryEnvelope; positivity

 theorem highHeatRawNumerator_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a V η bd : ℝ) (ha : 0 < a) (hbd : 0 ≤ bd)
    (p g w : Fin n → ℝ) (hp : ∀ i, |p i| ≤ bd) (hw : ∀ i, |w i| ≤ 1)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hMass : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u) (y : Fin n → Fin 3) :
    |highHeatRawNumerator a V η p g w φ c y| ≤ η^2*bd^n*(n : ℝ)/a^2 := by
  have hterm (i : Fin n) : |(w i)^2*highResponseVarianceTerm a V η g w φ c y i| ≤ 1/a^2 := by
    have hW : (w i)^2 ≤ 1 := by simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hw i)
    have hv := high_response_variance_term_abs_bound a V η ha g w φ c hMass y i
    rw [abs_mul, abs_sq]
    exact (mul_le_mul hW hv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have hsum : |∑ i, (w i)^2*highResponseVarianceTerm a V η g w φ c y i| ≤ (n : ℝ)/a^2 := by
    have h := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun i _ => hterm i))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv, mul_one, one_mul] using h
  unfold highHeatRawNumerator
  rw [abs_neg, abs_mul, abs_mul, abs_sq]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p bd hbd hp) (sq_nonneg η))
    hsum (abs_nonneg _) (mul_nonneg (sq_nonneg η) (pow_nonneg hbd n))).trans_eq (by ring)

 theorem highHeatRawNumerator_sum_square_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a V η bd : ℝ) (ha : 0 < a) (hbd : 0 ≤ bd)
    (p g w : Fin n → ℝ) (hp : ∀ i, |p i| ≤ bd) (hw : ∀ i, |w i| ≤ 1)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hMass : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u) :
    (∑ y : Fin n → Fin 3, highHeatRawNumerator a V η p g w φ c y^2) ≤ highHeatGeometryEnvelope n bd a η := by
  have hy (y : Fin n → Fin 3) : highHeatRawNumerator a V η p g w φ c y^2 ≤ (η^2*bd^n*(n : ℝ)/a^2)^2 := by
    have h := highHeatRawNumerator_abs_le a V η bd ha hbd p g w hp hw φ c hMass y
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h
  exact (Finset.sum_le_sum (s := Finset.univ) (fun y _ => hy y)).trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]; rfl)

 theorem highHeat_fullSpatialPatchDesign_real_univ (d n : ℕ) :
    (fullSpatialPatchDesign d n).real univ = (2 : ℝ)^(d*n) := by
  simp only [measureReal_def, fullSpatialPatchDesign, Measure.pi_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow, Measure.restrict_apply_univ]
  change volume.real (spatialPatchBox d)^n = _
  rw [spatialPatchBox_real_volume, ← pow_mul]

 theorem highHeatGeometryEnvelope_integrable_and_integral (d n : ℕ) (bd a η : ℝ) :
    Integrable (fun _ : Fin n → Covariate d => highHeatGeometryEnvelope n bd a η) (fullSpatialPatchDesign d n) ∧
    (∫ _ : Fin n → Covariate d, highHeatGeometryEnvelope n bd a η ∂fullSpatialPatchDesign d n) =
      (3 : ℝ)^n*highHeatSpatialBudget d n bd a η := by
  refine ⟨integrable_const _, ?_⟩
  rw [integral_const, smul_eq_mul, highHeat_fullSpatialPatchDesign_real_univ]
  unfold highHeatGeometryEnvelope highHeatSpatialBudget
  ring

end NearlyMinimax
