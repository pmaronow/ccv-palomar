module

public import NearlyMinimax.HighCardinalRawEnvelope
public import NearlyMinimax.FinePairSpatialEnergy


@[expose] public section

/-! Full spatial energy of the genuine matched cardinal packet numerator.
The two deterministic envelopes are integrated against the actual Q^n law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem responseMatrixAction_spatial_matrix_measurable {d n F : ℕ} (q : ℕ) (C a V η : ℝ)
    (g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun U => g U i)) (hw : ∀ i, Measurable (fun U => w U i))
    (A : (Fin n → Covariate d) → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ γ δ, Measurable (fun U => A U γ δ))
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun U => responseMatrixAction q C (A U) c (fun v =>
      highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)) := by
  simp_rw [← highResponseMark_action]
  apply Finset.measurable_sum
  intro h _
  apply Measurable.mul _ (highResponseProduct_spatial_measurable a V η g w hg hw _ y)
  unfold highResponseMarkWeight covarianceWeight
  exact (((hA _ _).const_mul _).mul_const _).mul_const _ |>.const_mul _

 theorem highResponseVarianceTerm_spatial_measurable {d n F : ℕ} (a V η : ℝ)
    (g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun U => g U i)) (hw : ∀ i, Measurable (fun U => w U i))
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) (i : Fin n) :
    Measurable (fun U => highResponseVarianceTerm a V η (g U) (w U)
      (fun i => highFrameFeature (U i)) c y i) := by
  unfold highResponseVarianceTerm
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro l _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  exact (hg l).add ((measurable_const.mul (hw l)).mul
    (Finset.measurable_sum _ (fun γ _ => (highFrameFeature_spatial_measurable l γ).mul_const _)))

 theorem highResponseDefect_spatial_matrix_measurable {d n F : ℕ} (q : ℕ) (C a V η : ℝ)
    (g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun U => g U i)) (hw : ∀ i, Measurable (fun U => w U i))
    (A : (Fin n → Covariate d) → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ γ δ, Measurable (fun U => A U γ δ))
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun U => highResponseDefect q C a V η (A U) (g U) (w U)
      (fun i => highFrameFeature (U i)) c y) := by
  unfold highResponseDefect
  simp_rw [high_response_quadratic_eq_exact_rule]
  exact (responseMatrixAction_spatial_matrix_measurable q C a V η g w hg hw A hA c y).sub
    (responseMatrixAction_spatial_matrix_measurable n C a V η g w hg hw A hA c y)

 def cardinalRawSpatialEnergyBudget (d n q : ℕ) (bd C a ρ η T : ℝ) : ℝ :=
  2 * cardinalRawAliasCoefficient n bd a η ^ 2 *
      ((n : ℝ)^2 * (2 : ℝ)^d * cardinalDefectSquareBudget d n T) +
    2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
      ((n : ℝ)^2 * (2 : ℝ)^d *
        ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^(n-1))

 theorem highCardinalRawNumerator_spatial_square_integrable_and_le {d n F : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hn2 : 2 ≤ n) (ad bd : ℝ) (haD : 0 < ad) (hab : ad < bd)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hnm : n ≤ m) (hnD : n ≤ D)
    (hnF : n ≤ F) (hq : 1 ≤ q) (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hpmeas : ∀ i, Measurable (fun U => p U i))
    (hgmeas : ∀ i, Measurable (fun U => g U i))
    (hwmeas : ∀ i, Measurable (fun U => w U i))
    (hpD : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, p U i ∈ Icc ad bd)
    (hg : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |g U i| ≤ ρ/2)
    (hw : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |w U i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    Integrable (fun U => highCardinalRawNumerator ad bd (spatialInterpolationLambda d) T m D q
      C a V η U (p U) (g U) (w U) c y ^ 2) (fullSpatialPatchDesign d n) ∧
    (∫ U, highCardinalRawNumerator ad bd (spatialInterpolationLambda d) T m D q
      C a V η U (p U) (g U) (w U) c y ^ 2 ∂fullSpatialPatchDesign d n) ≤
        cardinalRawSpatialEnergyBudget d n q bd C a ρ η T := by
  classical
  let lam := spatialInterpolationLambda d
  have hlam : 0 ≤ lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  let R := fun U => highCardinalRawNumerator ad bd lam T m D q C a V η U (p U) (g U) (w U) c y
  let A := cardinalRawAliasCoefficient n bd a η
  let B := cardinalRawTaylorCoefficient n q bd C a ρ η
  let Z := fun U : Fin n → Covariate d => ∑ i, cardinalWeightDefect i lam T U
  let E := fun U : Fin n → Covariate d => spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U)
  let S := fun U => η^2 * (∏ i, p U i) * ∑ i, (w U i)^2 * (integratedCardinalWeight lam T U i-1) *
    highResponseVarianceTerm a V η (g U) (w U) (fun i => highFrameFeature (U i)) c y i +
    (∏ i, p U i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
      (g U) (w U) (fun i => highFrameFeature (U i)) c y
  have hS : Measurable S := by
    apply Measurable.add
    · exact ((Finset.measurable_prod _ (fun i _ => hpmeas i)).const_mul _).mul
        (Finset.measurable_sum _ (fun i _ =>
          (((hwmeas i).pow_const 2).mul ((integrated_cardinal_weight_continuous i lam hT).measurable.sub_const 1)).mul
            (highResponseVarianceTerm_spatial_measurable a V η g w hgmeas hwmeas c y i)))
    · exact (Finset.measurable_prod _ (fun i _ => hpmeas i)).mul
        (highResponseDefect_spatial_matrix_measurable q C a V η g w hgmeas hwmeas _
          (fun γ δ => (integrated_cardinal_matrix_continuous lam hT γ δ).measurable) c y)
  have heq : R =ᵐ[fullSpatialPatchDesign d n] S := by
    filter_upwards [fullSpatialPatchDesign_ae_coordinate_bound, hpD] with U hU hpU
    exact highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q (by omega)
      hnm hnD hnF C a V η (lt_of_lt_of_le zero_lt_one hC).ne' U hU (p U) (g U) (w U) hpU c y
  have hRmeas : AEStronglyMeasurable R (fullSpatialPatchDesign d n) :=
    hS.aestronglyMeasurable.congr heq.symm
  have hZ : Integrable (fun U => Z U ^ 2) (fullSpatialPatchDesign d n) := by
    have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) Finset.univ
      (fun i U => cardinalWeightDefect i lam T U)
      (fun i _ => cardinalWeightDefect_measurable i lam hT)
      (fun i _ => cardinalWeightDefect_square_integrable i hlam hT)
    simpa only [abs_of_nonneg (cardinalWeightDefect_mem_unit _ hlam T _).1] using h
  have hE := integratedCardinalMatrix_full_square_integrable (D := F) hd hn2 hT
  have hUpper : Integrable (fun U => 2*A^2*Z U^2+2*B^2*E U^2) (fullSpatialPatchDesign d n) :=
    (hZ.const_mul _).add (hE.const_mul _)
  have hbound : ∀ᵐ U ∂fullSpatialPatchDesign d n, R U^2 ≤ 2*A^2*Z U^2+2*B^2*E U^2 := by
    filter_upwards [fullSpatialPatchDesign_ae_coordinate_bound, hpD, hg, hw] with U hU hpU hgU hwU
    exact highCardinalRawNumerator_square_bound_of_chart ad bd lam haD hab hlam hT m D q
      (by omega) hnm hnD hnF hq C a V η ρ hC ha hη hρ hηρ U hU (p U) (g U) (w U) hpU hgU hwU c hc hp y
  have hR : Integrable (fun U => R U^2) (fullSpatialPatchDesign d n) :=
    hUpper.mono' (hRmeas.pow 2) (by filter_upwards [hbound] with U hU; simpa only [Real.norm_eq_abs, abs_sq] using hU)
  refine ⟨hR, (integral_mono_ae hR hUpper hbound).trans ?_⟩
  rw [integral_add (hZ.const_mul _) (hE.const_mul _), integral_const_mul, integral_const_mul]
  have hZa := cardinalWeightDefect_sum_square_integral_le (d := d) (by omega) hn2 hT
  have hEa := integratedCardinalMatrix_full_square_integral_le (D := F) hd hn2 hT
  exact (add_le_add (mul_le_mul_of_nonneg_left hZa (by positivity : 0 ≤ 2*A^2))
    (mul_le_mul_of_nonneg_left hEa (by positivity : 0 ≤ 2*B^2))).trans_eq (by rfl)

end NearlyMinimax
