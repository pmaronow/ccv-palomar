module

public import NearlyMinimax.HighSpatialEnvelopes
public import NearlyMinimax.AffineNuisanceNumerator


@[expose] public section

/-! Literal supremum-before-spatial-integration norms for the actual
cardinal and radial count-two signed defects. Measurability and continuity
are proved from their finite response formulas, rather than assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

def highDefectPatchSet (d n : ℕ) : Set (Fin n → Covariate d) :=
  {U | ∀ i r, |U i r| ≤ 1}

theorem highDefectPatchSet_measurable (d n : ℕ) : MeasurableSet (highDefectPatchSet d n) := by
  unfold highDefectPatchSet
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro r
  exact measurableSet_le (((measurable_pi_apply r).comp (measurable_pi_apply i)).abs) measurable_const

theorem compactNuisanceEnergy_congrOn {P X Y : Type*} [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace X] [Fintype Y]
    (K : Set P) (F G : P → X → Y → ℝ) (x : X)
    (h : ∀ p ∈ K, ∀ y, F p x y = G p x y) :
    compactNuisanceEnergy K F x = compactNuisanceEnergy K G x := by
  apply congrArg sSup
  apply Set.image_congr
  intro p hp
  exact Finset.sum_congr rfl (fun y _ => congrArg (fun t : ℝ => t^2) (h p hp y))

theorem ternaryMeanDerivative_continuous_comp {P : Type*} [TopologicalSpace P]
    (a : ℝ) (f : P → ℝ) (hf : Continuous f) (y : Fin 3) :
    Continuous (fun p => ternaryMeanDerivative a (f p) y) := by
  fin_cases y <;> simp only [ternaryMeanDerivative, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop

def radialDefectPolynomial {d F : ℕ} (a η N : ℝ)
    (z : LocalNuisance (HighFrameIndex d F) 2)
    (U : Fin 2 → Covariate d) (y : Fin 2 → Fin 3) : ℝ :=
  let w := fun i => highWindowTensor d (U i)
  let f := coefficientRegression η z.2.2.1 w (fun i => highFrameFeature (U i)) z.2.1
  η^2*w 0*w 1*z.1 0*z.1 1*finePairDistanceFactor N (U 0) (U 1)*
    ternaryMeanDerivative a (f 0) (y 0)*ternaryMeanDerivative a (f 1) (y 1)

theorem radialDefectPolynomial_continuous_nuisance {d F : ℕ} (a η N : ℝ)
    (U : Fin 2 → Covariate d) (y : Fin 2 → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) 2 => radialDefectPolynomial a η N z U y) := by
  unfold radialDefectPolynomial
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · apply ternaryMeanDerivative_continuous_comp
      unfold coefficientRegression
      fun_prop
  · apply ternaryMeanDerivative_continuous_comp
    unfold coefficientRegression
    fun_prop

theorem radialDefectPolynomial_spatial_measurable {d F : ℕ} (a η N : ℝ)
    (z : LocalNuisance (HighFrameIndex d F) 2) (y : Fin 2 → Fin 3) :
    Measurable (fun U => radialDefectPolynomial a η N z U y) := by
  unfold radialDefectPolynomial
  have hw (i : Fin 2) : Measurable (fun U : Fin 2 → Covariate d => highWindowTensor d (U i)) :=
    (highWindowTensor_contDiff d).continuous.measurable.comp (measurable_pi_apply i)
  have hf (i : Fin 2) : Measurable (fun U : Fin 2 → Covariate d =>
      coefficientRegression η z.2.2.1 (fun i => highWindowTensor d (U i))
        (fun i => highFrameFeature (U i)) z.2.1 i) := by
    unfold coefficientRegression
    have hs : Measurable (fun U : Fin 2 → Covariate d =>
        ∑ γ : HighFrameIndex d F, highFrameFeature (U i) γ * z.2.1 γ) :=
      Finset.measurable_sum (Finset.univ : Finset (HighFrameIndex d F))
        (fun γ _ => (highFrameFeature_spatial_measurable i γ).mul_const (z.2.1 γ))
    exact (measurable_const : Measurable (fun _ : Fin 2 → Covariate d => z.2.2.1 i)).add
      (((hw i).const_mul η).mul hs)
  have hdist : Measurable (fun U : Fin 2 → Covariate d => exactEuclideanDistance (U 0) (U 1)) := by
    have hcoord (i : Fin 2) (r : Fin d) : Measurable (fun U : Fin 2 → Covariate d => U i r) :=
      (measurable_pi_apply r).comp (measurable_pi_apply i)
    unfold exactEuclideanDistance spatialSquaredDistance
    apply Real.continuous_sqrt.measurable.comp
    exact Finset.measurable_sum (Finset.univ : Finset (Fin d))
      (fun r _ => ((hcoord 1 r).sub (hcoord 0 r)).pow_const 2)
  have hd : Measurable (fun U : Fin 2 → Covariate d => finePairDistanceFactor N (U 0) (U 1)) := by
    unfold finePairDistanceFactor
    exact (measurable_const.add (hdist.const_mul N)).mul ((hdist.const_mul N).neg.exp)
  have hbase : Measurable (fun U : Fin 2 → Covariate d =>
      η^2 * highWindowTensor d (U 0) * highWindowTensor d (U 1) * z.1 0 * z.1 1 *
        finePairDistanceFactor N (U 0) (U 1)) :=
    (((((hw 0).const_mul (η^2)).mul (hw 1)).mul_const (z.1 0)).mul_const (z.1 1)).mul hd
  exact (hbase.mul (ternaryMeanDerivative_measurable_comp a _ (hf 0) (y 0))).mul
    (ternaryMeanDerivative_measurable_comp a _ (hf 1) (y 1))

def radialDefectPatchPolynomial {d F : ℕ} (a η N : ℝ)
    (z : LocalNuisance (HighFrameIndex d F) 2)
    (U : Fin 2 → Covariate d) (y : Fin 2 → Fin 3) : ℝ :=
  if U ∈ highDefectPatchSet d 2 then radialDefectPolynomial a η N z U y else 0

theorem radialDefectPatchPolynomial_measurable {d F : ℕ} (a η N : ℝ)
    (z : LocalNuisance (HighFrameIndex d F) 2) (y : Fin 2 → Fin 3) :
    Measurable (fun U => radialDefectPatchPolynomial a η N z U y) :=
  (radialDefectPolynomial_spatial_measurable a η N z y).indicator (highDefectPatchSet_measurable d 2)

theorem radialDefectPatchPolynomial_continuous_nuisance {d F : ℕ} (a η N : ℝ)
    (U : Fin 2 → Covariate d) (y : Fin 2 → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) 2 => radialDefectPatchPolynomial a η N z U y) := by
  unfold radialDefectPatchPolynomial
  split_ifs
  · exact radialDefectPolynomial_continuous_nuisance a η N U y
  · exact continuous_const

section Pair
variable {d F : ℕ} [NeZero d] (hF : 3 ≤ F)
  (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hTN : T0 ≤ N)
  (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
  (Cmodel : ModelConstants d) (Q : LowSmoothnessTernaryConstants Cmodel)
  (Cfr η : ℝ) (hCfr : 1 ≤ Cfr) (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2)
local notation "K" => localNuisanceSet (HighFrameIndex d F) 2 ad bd Cfr Q.ρ Q.v

def radialActualNuisanceNumerator (z : LocalNuisance (HighFrameIndex d F) 2)
    (U : Fin 2 → Covariate d) (y : Fin 2 → Fin 3) : ℝ :=
  finePairCountTwoRawNumerator ad bd T0 N D M q Cfr Q.a z.2.2.2 η U
    z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) z.2.1 y

include hF haD hab hT0 hTN hD hM hq hCfr
theorem radialActualNuisanceNumerator_eq_polynomial
    (z : LocalNuisance (HighFrameIndex d F) 2) (hz : z ∈ K)
    (U : Fin 2 → Covariate d) (hU : U ∈ highDefectPatchSet d 2) (y : Fin 2 → Fin 3) :
    radialActualNuisanceNumerator ad bd T0 N D M q Cmodel Q Cfr η z U y =
      radialDefectPatchPolynomial Q.a η N z U y := by
  have hp := (localNuisanceSet_guards _ 2 ad bd Cfr Q.ρ Q.v z hz).1
  simpa only [radialActualNuisanceNumerator, finePairCountTwoRawNumerator, radialDefectPatchPolynomial, if_pos hU,
    radialDefectPolynomial, finePairDistanceFactor] using
      finePairThreeRow_count_two_numerator hF ad bd T0 N haD hab hT0 hTN D M q hD hM hq
        Cfr Q.a z.2.2.2 η (lt_of_lt_of_le zero_lt_one hCfr).ne'
        U hU z.1 hp z.2.2.1 (fun i => highWindowTensor d (U i)) z.2.1 y

theorem radialActualNuisanceEnergy_eq_patch_ae :
    compactNuisanceEnergy K (radialActualNuisanceNumerator ad bd T0 N D M q Cmodel Q Cfr η) =ᵐ[
      fullSpatialPatchDesign d 2] compactNuisanceEnergy K (radialDefectPatchPolynomial (F := F) Q.a η N) := by
  filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
  apply compactNuisanceEnergy_congrOn
  intro z hz y
  exact radialActualNuisanceNumerator_eq_polynomial hF ad bd T0 N haD hab hT0 hTN D M q hD hM hq
    Cmodel Q Cfr η hCfr z hz U hU y

include hη hηρ
theorem radialActualNuisanceEnergy_integrable_and_bound (hN : 0 < N) :
    Integrable (compactNuisanceEnergy K
      (radialActualNuisanceNumerator ad bd T0 N D M q Cmodel Q Cfr η)) (fullSpatialPatchDesign d 2) ∧
    (∫ U, compactNuisanceEnergy K
      (radialActualNuisanceNumerator ad bd T0 N D M q Cmodel Q Cfr η) U ∂fullSpatialPatchDesign d 2) ≤
      9*finePairCountTwoSpatialBudget d bd Q.a Q.ρ η N := by
  have hEnv := finePairCountTwoGeometryEnvelope_integrable_and_le Cmodel.dimension_pos bd Q.a Q.ρ η hN
  have hi := compactNuisanceEnergy_integrable_and_bound (fullSpatialPatchDesign d 2) K
    (localNuisanceSet_isCompact _ _ _ _ _ _ _) (localNuisanceSet_nonempty _ _ hab.le
      (by linarith) Q.ρ_pos.le) (radialDefectPatchPolynomial (F := F) Q.a η N)
    (fun z _ y => radialDefectPatchPolynomial_measurable Q.a η N z y)
    (fun U y => (radialDefectPatchPolynomial_continuous_nuisance Q.a η N U y).continuousOn)
    (finePairCountTwoGeometryEnvelope bd Q.a Q.ρ η N) hEnv.1 (by
      intro z hz U
      by_cases hU : U ∈ highDefectPatchSet d 2
      · have hEq (y) := radialActualNuisanceNumerator_eq_polynomial hF ad bd T0 N haD hab hT0 hTN D M q hD hM hq
          Cmodel Q Cfr η hCfr z hz U hU y
        simp_rw [← hEq]
        obtain ⟨hp,hc,hg,_⟩ := localNuisanceSet_guards _ 2 ad bd Cfr Q.ρ Q.v z hz
        have hw (i : Fin 2) : |highWindowTensor d (U i)| ≤ 1 := by
          rw [abs_of_nonneg (highWindowTensor_nonneg _ _)]
          exact highWindowTensor_le_one _ _
        have hU2 : ∀ i r, |U i r| ≤ 2 := fun i r => (hU i r).trans (by norm_num)
        exact finePairCountTwoRawNumerator_sum_square_le_geometry hF ad bd T0 N haD hab hT0 hTN D M q hD hM hq
          Cfr Q.a z.2.2.2 η Q.ρ (lt_of_lt_of_le zero_lt_one hCfr).ne' Q.a_pos Q.ρ_pos.le
          U hU z.1 z.2.2.1 _ hp hw z.2.1 (fun i => highFrameCoefficientRegression_abs_le Cfr η Q.ρ
            hCfr hη hηρ U hU2 z.2.2.1 _ hg hw z.2.1 hc i)
      · simp only [radialDefectPatchPolynomial, if_neg hU, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
        exact finePairCountTwoGeometryEnvelope_nonneg _ _ _ _ _ U)
  have heq := radialActualNuisanceEnergy_eq_patch_ae hF ad bd T0 N haD hab hT0 hTN D M q hD hM hq
    Cmodel Q Cfr η hCfr
  exact ⟨hi.1.congr heq.symm, (integral_congr_ae heq).trans_le (hi.2.trans hEnv.2)⟩
end Pair

theorem defectResponseMatrixAction_continuous_nuisance {d n F : ℕ}
    (q : ℕ) (C a η : ℝ) (A : HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (U : Fin n → Covariate d) (w : Fin n → ℝ) (y : Fin n → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) n =>
      responseMatrixAction q C A z.2.1 (fun v =>
        highResponseProduct a z.2.2.2 η z.2.2.1 w (fun i => highFrameFeature (U i)) v y)) := by
  simp_rw [← highResponseMark_action]
  apply continuous_finsetSum
  intro h _
  apply Continuous.const_mul
  unfold highResponseProduct
  apply continuous_finset_prod
  intro i _
  apply ternaryMass_continuous_both
  · unfold coefficientRegression coefficientReset
    fun_prop
  · fun_prop

theorem defectResponseVarianceTerm_continuous_nuisance {d n F : ℕ}
    (a η : ℝ) (U : Fin n → Covariate d) (w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) n =>
      highResponseVarianceTerm a z.2.2.2 η z.2.2.1 w (fun i => highFrameFeature (U i)) z.2.1 y i) := by
  unfold highResponseVarianceTerm
  apply Continuous.const_mul
  apply continuous_finset_prod
  intro l _
  apply ternaryMass_continuous_both
  · unfold coefficientRegression
    fun_prop
  · fun_prop

def cardinalDefectPolynomial {d n F : ℕ} (q : ℕ) (C a η T : ℝ)
    (z : LocalNuisance (HighFrameIndex d F) n) (U : Fin n → Covariate d)
    (y : Fin n → Fin 3) : ℝ :=
  let w := fun i => highWindowTensor d (U i)
  η^2*(∏ i, z.1 i)*∑ i, (w i)^2*(integratedCardinalWeight (spatialInterpolationLambda d) T U i-1)*
    highResponseVarianceTerm a z.2.2.2 η z.2.2.1 w (fun i => highFrameFeature (U i)) z.2.1 y i +
  (∏ i, z.1 i)*highResponseDefect q C a z.2.2.2 η
    (integratedCardinalMatrix (spatialInterpolationLambda d) T U) z.2.2.1 w
    (fun i => highFrameFeature (U i)) z.2.1 y

theorem cardinalDefectPolynomial_continuous_nuisance {d n F : ℕ}
    (q : ℕ) (C a η T : ℝ) (U : Fin n → Covariate d) (y : Fin n → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) n => cardinalDefectPolynomial q C a η T z U y) := by
  unfold cardinalDefectPolynomial
  apply Continuous.add
  · apply Continuous.mul
    · fun_prop
    · apply continuous_finsetSum
      intro i _
      exact (defectResponseVarianceTerm_continuous_nuisance a η U
        (fun i => highWindowTensor d (U i)) y i).const_mul _
  · apply Continuous.mul
    · fun_prop
    · unfold highResponseDefect
      simp_rw [high_response_quadratic_eq_exact_rule]
      exact (defectResponseMatrixAction_continuous_nuisance q C a η _ U _ y).sub
        (defectResponseMatrixAction_continuous_nuisance n C a η _ U _ y)

theorem cardinalDefectPolynomial_spatial_measurable {d n F : ℕ}
    (q : ℕ) (C a η : ℝ) {T : ℝ} (hT : 1 ≤ T)
    (z : LocalNuisance (HighFrameIndex d F) n) (y : Fin n → Fin 3) :
    Measurable (fun U => cardinalDefectPolynomial q C a η T z U y) := by
  have hw (i : Fin n) : Measurable (fun U : Fin n → Covariate d => highWindowTensor d (U i)) :=
    (highWindowTensor_contDiff d).continuous.measurable.comp (measurable_pi_apply i)
  have hA (γ δ : HighFrameIndex d F) : Measurable (fun U : Fin n → Covariate d =>
      integratedCardinalMatrix (spatialInterpolationLambda d) T U γ δ) :=
    (integrated_cardinal_matrix_continuous (n := n) (spatialInterpolationLambda d) hT γ δ).measurable
  unfold cardinalDefectPolynomial
  apply Measurable.add
  · apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact (((hw i).pow_const 2).mul
      ((integrated_cardinal_weight_continuous i (spatialInterpolationLambda d) hT).measurable.sub_const 1)).mul
        (highResponseVarianceTerm_spatial_measurable a z.2.2.2 η (fun _ => z.2.2.1)
          (fun U i => highWindowTensor d (U i)) (fun _ => measurable_const) hw z.2.1 y i)
  · exact (highResponseDefect_spatial_matrix_measurable q C a z.2.2.2 η (fun _ => z.2.2.1)
      (fun U i => highWindowTensor d (U i)) (fun _ => measurable_const) hw
      (fun U => integratedCardinalMatrix (spatialInterpolationLambda d) T U) hA z.2.1 y).const_mul _

def cardinalDefectPatchPolynomial {d n F : ℕ} (q : ℕ) (C a η T : ℝ)
    (z : LocalNuisance (HighFrameIndex d F) n) (U : Fin n → Covariate d)
    (y : Fin n → Fin 3) : ℝ :=
  if U ∈ highDefectPatchSet d n then cardinalDefectPolynomial q C a η T z U y else 0

theorem cardinalDefectPatchPolynomial_measurable {d n F : ℕ}
    (q : ℕ) (C a η : ℝ) {T : ℝ} (hT : 1 ≤ T)
    (z : LocalNuisance (HighFrameIndex d F) n) (y : Fin n → Fin 3) :
    Measurable (fun U => cardinalDefectPatchPolynomial q C a η T z U y) :=
  (cardinalDefectPolynomial_spatial_measurable q C a η hT z y).indicator (highDefectPatchSet_measurable d n)

theorem cardinalDefectPatchPolynomial_continuous_nuisance {d n F : ℕ}
    (q : ℕ) (C a η T : ℝ) (U : Fin n → Covariate d) (y : Fin n → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) n => cardinalDefectPatchPolynomial q C a η T z U y) := by
  unfold cardinalDefectPatchPolynomial
  split_ifs
  · exact cardinalDefectPolynomial_continuous_nuisance q C a η T U y
  · exact continuous_const

section Cardinal
variable {d n F : ℕ} (ad bd : ℝ) (haD : 0 < ad) (hab : ad < bd)
  (T : ℝ) (hT : 1 ≤ T) (m D q : ℕ) (hn : 3 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D) (hnF : n ≤ F)
  (Cmodel : ModelConstants d) (Q : LowSmoothnessTernaryConstants Cmodel)
  (Cfr η : ℝ) (hCfr : 1 ≤ Cfr) (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2)
local notation "K" => localNuisanceSet (HighFrameIndex d F) n ad bd Cfr Q.ρ Q.v

def cardinalActualNuisanceNumerator (z : LocalNuisance (HighFrameIndex d F) n)
    (U : Fin n → Covariate d) (y : Fin n → Fin 3) : ℝ :=
  highCardinalRawNumerator ad bd (spatialInterpolationLambda d) T m D q Cfr Q.a z.2.2.2 η U
    z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) z.2.1 y

include haD hab hT hn hnm hnD hnF hCfr
theorem cardinalActualNuisanceNumerator_eq_polynomial
    (z : LocalNuisance (HighFrameIndex d F) n) (hz : z ∈ K)
    (U : Fin n → Covariate d) (hU : U ∈ highDefectPatchSet d n) (y : Fin n → Fin 3) :
    cardinalActualNuisanceNumerator ad bd T m D q Cmodel Q Cfr η z U y =
      cardinalDefectPatchPolynomial q Cfr Q.a η T z U y := by
  have hp := (localNuisanceSet_guards _ n ad bd Cfr Q.ρ Q.v z hz).1
  simpa only [cardinalActualNuisanceNumerator, cardinalDefectPatchPolynomial, if_pos hU,
    cardinalDefectPolynomial] using highCardinalRawNumerator_eq_alias_defect ad bd
      (spatialInterpolationLambda d) haD hab (by unfold spatialInterpolationLambda; positivity)
      hT m D q (by omega) hnm hnD hnF Cfr Q.a z.2.2.2 η (lt_of_lt_of_le zero_lt_one hCfr).ne'
      U (fun i r => (hU i r).trans (by norm_num)) z.1 z.2.2.1
      (fun i => highWindowTensor d (U i)) hp z.2.1 y

theorem cardinalActualNuisanceEnergy_eq_patch_ae :
    compactNuisanceEnergy K (cardinalActualNuisanceNumerator ad bd T m D q Cmodel Q Cfr η) =ᵐ[
      fullSpatialPatchDesign d n] compactNuisanceEnergy K (cardinalDefectPatchPolynomial (F := F) q Cfr Q.a η T) := by
  filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
  apply compactNuisanceEnergy_congrOn
  intro z hz y
  exact cardinalActualNuisanceNumerator_eq_polynomial ad bd haD hab T hT m D q hn hnm hnD hnF
    Cmodel Q Cfr η hCfr z hz U hU y

include hη hηρ
theorem cardinalActualNuisanceEnergy_integrable_and_le_geometry (hd : 5 ≤ d) (hq : 1 ≤ q) :
    Integrable (compactNuisanceEnergy K
      (cardinalActualNuisanceNumerator ad bd T m D q Cmodel Q Cfr η)) (fullSpatialPatchDesign d n) ∧
    (∫ U, compactNuisanceEnergy K
      (cardinalActualNuisanceNumerator ad bd T m D q Cmodel Q Cfr η) U ∂fullSpatialPatchDesign d n) ≤
      ∫ U, cardinalGeometryEnvelope (F := F) q bd Cfr Q.a Q.ρ η T U ∂fullSpatialPatchDesign d n := by
  have hEnv := cardinalGeometryEnvelope_integrable_and_le (F := F) hd (by omega : 2 ≤ n) q bd Cfr Q.a Q.ρ η hT
  have hi := compactNuisanceEnergy_integrable_and_bound (fullSpatialPatchDesign d n) K
    (localNuisanceSet_isCompact _ _ _ _ _ _ _) (localNuisanceSet_nonempty _ _ hab.le
      (by linarith) Q.ρ_pos.le) (cardinalDefectPatchPolynomial (F := F) q Cfr Q.a η T)
    (fun z _ y => cardinalDefectPatchPolynomial_measurable q Cfr Q.a η hT z y)
    (fun U y => (cardinalDefectPatchPolynomial_continuous_nuisance q Cfr Q.a η T U y).continuousOn)
    (cardinalGeometryEnvelope (F := F) q bd Cfr Q.a Q.ρ η T) hEnv.1 (by
      intro z hz U
      by_cases hU : U ∈ highDefectPatchSet d n
      · have hEq (y) := cardinalActualNuisanceNumerator_eq_polynomial ad bd haD hab T hT m D q hn hnm hnD hnF
          Cmodel Q Cfr η hCfr z hz U hU y
        simp_rw [← hEq]
        obtain ⟨hp,hc,hg,hV⟩ := localNuisanceSet_guards _ n ad bd Cfr Q.ρ Q.v z hz
        have hw (i : Fin n) : |highWindowTensor d (U i)| ≤ 1 := by
          rw [abs_of_nonneg (highWindowTensor_nonneg _ _)]
          exact highWindowTensor_le_one _ _
        have hprob : ∀ f : ℝ, |f| ≤ Q.ρ → ∀ y, 0 ≤ ternaryMass Q.a f z.2.2.2 y :=
          fun f hf y => Q.c_pos.le.trans ((Q.legal f _ hf hV).2.2.1 y)
        exact highCardinalRawNumerator_sum_square_le_geometry ad bd haD hab hT m D q (by omega)
          hnm hnD hnF hq Cfr Q.a z.2.2.2 η Q.ρ hCfr Q.a_pos hη Q.ρ_pos.le hηρ
          U (fun i r => (hU i r).trans (by norm_num)) z.1 z.2.2.1 _ hp hg hw z.2.1 hc hprob
      · simp only [cardinalDefectPatchPolynomial, if_neg hU, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
        exact cardinalGeometryEnvelope_nonneg q bd Cfr Q.a Q.ρ η T U)
  have heq := cardinalActualNuisanceEnergy_eq_patch_ae ad bd haD hab T hT m D q hn hnm hnD hnF Cmodel Q Cfr η hCfr
  exact ⟨hi.1.congr heq.symm, (integral_congr_ae heq).trans_le hi.2⟩

theorem cardinalActualNuisanceEnergy_integrable_and_bound (hd : 5 ≤ d) (hq : 1 ≤ q) :
    Integrable (compactNuisanceEnergy K
      (cardinalActualNuisanceNumerator ad bd T m D q Cmodel Q Cfr η)) (fullSpatialPatchDesign d n) ∧
    (∫ U, compactNuisanceEnergy K
      (cardinalActualNuisanceNumerator ad bd T m D q Cmodel Q Cfr η) U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n*cardinalRawSpatialEnergyBudget d n q bd Cfr Q.a Q.ρ η T := by
  have h := cardinalActualNuisanceEnergy_integrable_and_le_geometry ad bd haD hab T hT m D q
    hn hnm hnD hnF Cmodel Q Cfr η hCfr hη hηρ hd hq
  exact ⟨h.1, h.2.trans (cardinalGeometryEnvelope_integrable_and_le (F := F) hd
    (by omega : 2 ≤ n) q bd Cfr Q.a Q.ρ η hT).2⟩
end Cardinal

end NearlyMinimax
