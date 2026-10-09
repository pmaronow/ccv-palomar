module

public import NearlyMinimax.FinePairCountTwoEnergy
public import NearlyMinimax.FinePairAliasSpatialEnergy


@[expose] public section

/-! Actual spatial energy of the complete three-row count-two numerator,
including the single heat correction and the true radial defect. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

 theorem ternaryMeanDerivative_measurable_comp {X : Type*} [MeasurableSpace X]
    (a : ℝ) (f : X → ℝ) (hf : Measurable f) (y : Fin 3) :
    Measurable (fun x => ternaryMeanDerivative a (f x) y) := by
  fin_cases y <;> simp only [ternaryMeanDerivative, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] <;> fun_prop

 def finePairCountTwoSpatialBudget (d : ℕ) (bd a ρ η N : ℝ) : ℝ :=
  (η^2*bd^2*((2*ρ+a)/a^2)^2)^2 * (6*(2 : ℝ)^d*spatialExponentialConstant d/N^d)

 theorem finePairCountTwoRawNumerator_spatial_square_integrable_and_le {d F : ℕ} [NeZero d]
    (hd : 0 < d) (hF : 3 ≤ F) (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd)
    (hT0 : 0 ≤ T0) (hN : T0 ≤ N) (hNpos : 0 < N) (D M q : ℕ)
    (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q) (C a V η ρ : ℝ)
    (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (p g w : (Fin 2 → Covariate d) → Fin 2 → ℝ)
    (hpmeas : ∀ i, Measurable (fun U => p U i))
    (hgmeas : ∀ i, Measurable (fun U => g U i))
    (hwmeas : ∀ i, Measurable (fun U => w U i))
    (hpD : ∀ᵐ U ∂fullSpatialPatchDesign d 2, ∀ i, p U i ∈ Icc ad bd)
    (hg : ∀ᵐ U ∂fullSpatialPatchDesign d 2, ∀ i, |g U i| ≤ ρ/2)
    (hw : ∀ᵐ U ∂fullSpatialPatchDesign d 2, ∀ i, |w U i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) (y : Fin 2 → Fin 3) :
    Integrable (fun U => finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U
      (p U) (g U) (w U) c y ^ 2) (fullSpatialPatchDesign d 2) ∧
    (∫ U, finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U
      (p U) (g U) (w U) c y ^ 2 ∂fullSpatialPatchDesign d 2) ≤
      finePairCountTwoSpatialBudget d bd a ρ η N := by
  let R : (Fin 2 → Covariate d) → ℝ := fun U => finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U (p U) (g U) (w U) c y
  let H := fun U : Fin 2 → Covariate d => finePairDistanceFactor N (U 0) (U 1)
  let K := η^2*bd^2*((2*ρ+a)/a^2)^2
  let f := fun (U : Fin 2 → Covariate d) i => coefficientRegression η (g U) (w U)
    (fun i => highFrameFeature (U i)) c i
  let S := fun U => η^2*w U 0*w U 1*p U 0*p U 1*H U *
    ternaryMeanDerivative a (f U 0) (y 0) * ternaryMeanDerivative a (f U 1) (y 1)
  have hfmeas (i) : Measurable (fun U => f U i) := by
    unfold f coefficientRegression
    exact (hgmeas i).add ((measurable_const.mul (hwmeas i)).mul
      (Finset.measurable_sum _ (fun γ _ => (highFrameFeature_spatial_measurable i γ).mul_const _)))
  have hXY : Measurable (fun U : Fin 2 → Covariate d => (U 0, U 1)) :=
    (measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2))
  have hdist : Measurable (fun U : Fin 2 → Covariate d => exactEuclideanDistance (U 0) (U 1)) :=
    exactEuclideanDistance_continuous.measurable.comp hXY
  have hHmeas : Measurable H := by
    unfold H finePairDistanceFactor
    exact (measurable_const.add (hdist.const_mul N)).mul ((hdist.const_mul N).neg.exp)
  have hS : Measurable S :=
    (((((((hwmeas 0).const_mul _).mul (hwmeas 1)).mul (hpmeas 0)).mul (hpmeas 1)).mul hHmeas).mul
      (ternaryMeanDerivative_measurable_comp a _ (hfmeas 0) (y 0))).mul
        (ternaryMeanDerivative_measurable_comp a _ (hfmeas 1) (y 1))
  have heq : R =ᵐ[fullSpatialPatchDesign d 2] S := by
    filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube, hpD] with U hU hpU
    exact finePairThreeRow_count_two_numerator hF ad bd T0 N haD hab hT0 hN D M q hD hM hq
      C a V η (lt_of_lt_of_le zero_lt_one hC).ne' U hU (p U) hpU (g U) (w U) c y
  have hRmeas := hS.aestronglyMeasurable.congr heq.symm
  have hbound : ∀ᵐ U ∂fullSpatialPatchDesign d 2, R U^2 ≤ K^2 * H U^2 := by
    filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube,
      fullSpatialPatchDesign_ae_coordinate_bound, hpD, hg, hw] with U hU hU2 hpU hgU hwU
    have hreg (i) : |f U i| ≤ ρ := highFrameCoefficientRegression_abs_le C η ρ hC hη hηρ
      U hU2 (g U) (w U) hgU hwU c hc i
    have h := finePairCountTwoRawNumerator_abs_le hF ad bd T0 N haD hab hT0 hN D M q hD hM hq
      C a V η ρ (lt_of_lt_of_le zero_lt_one hC).ne' ha hρ U hU (p U) (g U) (w U) hpU hwU c hreg y
    change |R U| ≤ K * H U at h
    have hh := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
    simpa only [sq_abs, mul_pow] using hh
  have hH : Integrable (fun U => H U^2) (fullSpatialPatchDesign d 2) :=
    (measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))).integrable_comp_of_integrable
      (finePairDistanceFactor_square_integrable hNpos)
  have hupper := hH.const_mul (K^2)
  have hR : Integrable (fun U => R U^2) (fullSpatialPatchDesign d 2) :=
    hupper.mono' (hRmeas.pow 2) (by filter_upwards [hbound] with U hU; simpa only [Real.norm_eq_abs, abs_sq] using hU)
  refine ⟨hR, (integral_mono_ae hR hupper hbound).trans ?_⟩
  rw [integral_const_mul]
  have hInt : (∫ U : Fin 2 → Covariate d, H U^2 ∂fullSpatialPatchDesign d 2) ≤
      6*(2 : ℝ)^d*spatialExponentialConstant d/N^d :=
    ((measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))).integral_comp
      (MeasurableEquiv.finTwoArrow : (Fin 2 → Covariate d) ≃ᵐ (Covariate d × Covariate d)).measurableEmbedding _).trans_le
      (finePairDistanceFactor_square_integral_le hd hNpos)
  exact (mul_le_mul_of_nonneg_left hInt (sq_nonneg K)).trans_eq rfl

end NearlyMinimax
