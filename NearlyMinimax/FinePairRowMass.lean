module

public import NearlyMinimax.FinePairRows
public import NearlyMinimax.FinePairTimeCost


@[expose] public section

/-! Nondegeneracy and exact activity costs of the actual fine-pair rows. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

theorem response_absolute_cost_ge_one (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) ≤ ∑ j : Fin (2*q+2), |responseWeight q j| := by
  calc
    (1 : ℝ) = |∑ j : Fin (2*q+2), responseWeight q j * responseNode q j ^ 2| := by
      rw [response_second_moment q hq]; norm_num
    _ ≤ ∑ j : Fin (2*q+2), |responseWeight q j * responseNode q j ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (2*q+2), |responseWeight q j| := by
      apply Finset.sum_le_sum
      intro j _
      have he : |responseNode q j ^ 2| = responseNode q j ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [abs_mul, he]
      apply mul_le_of_le_one_right (abs_nonneg _)
      have hj := responseNode_mem_unit q j
      nlinarith [hj.1, hj.2, sq_nonneg (responseNode q j)]

theorem ordinary_density_absolute_cost_pos (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (D : ℕ) :
    0 < ∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h| := by
  rw [densityPacketWeight_variation a b ha hab D 2 D (by norm_num)]
  have hb : b ≠ 0 := (ha.trans hab).ne'
  have hθ := densityMargin_zero_ne a b ha hab
  have hp : densityPacketPrefactor a b 2 ≠ 0 := by
    change (2 : ℝ)^2 / (2 : ℝ) * (b / densityMargin a b 0)^2 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (div_ne_zero hb hθ))
  have hn : 0 < (derivativeOrder D : ℝ) := by
    have he : 0 < derivativeOrder D := by unfold derivativeOrder; omega
    exact_mod_cast he
  exact mul_pos (mul_pos (abs_pos.mpr hp) (Real.cosh_pos _)) (pow_pos hn _)

theorem fine_density_absolute_cost_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    0 < ∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h| := by
  rw [finePairDensityWeight_variation a b ha hab M]
  have hp : finePairDensityPrefactor a b ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (ha.trans hab).ne') (pow_ne_zero _ (densityMargin_zero_ne a b ha hab))
  exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr hp)) (Real.cosh_pos _)

theorem finePairRowMass_unit (d : ℕ) (D M q : ℕ) (a b C T₀ N : ℝ) :
    finePairRowMass d D M q a b C T₀ N .unit =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      (∑ i, ∑ j, |finePairUnitMatrix d D i j|) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _)]
  simp only [separatedMatrixCost, integral_dirac]

theorem finePairRowMass_coarse (d : ℕ) [NeZero d] (D M q : ℕ) (a b C T₀ N : ℝ)
    (hT : 0 ≤ T₀) :
    finePairRowMass d D M q a b C T₀ N .coarse =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * (T₀^2/2)) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation _ _ _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    highPacketSignedMeasure_totalVariation _ _ _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    finePairTimeMatrix_cost_integral d 0 T₀ le_rfl hT]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]

theorem finePairRowMass_fine (d : ℕ) [NeZero d] (D M q : ℕ) (a b C T₀ N : ℝ)
    (hT : 0 ≤ T₀) (hTN : T₀ ≤ N) :
    finePairRowMass d D M q a b C T₀ N .fine =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-T₀^2)/2)) := by
  rw [finePairRowMass, finePairPacketMarkMass]
  rw [signedMarkMass_eq_variation _ _ (finePairPacketWeight_integrable _ a b M q C _
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _))]
  change ((finePairPacketSignedMeasure _ a b M q C _).variation univ).toReal = _
  rw [finePairPacketSignedMeasure_totalVariation _ a b M q C _
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _),
    finePairTimeMatrix_cost_integral d T₀ N hT hTN]

end NearlyMinimax
