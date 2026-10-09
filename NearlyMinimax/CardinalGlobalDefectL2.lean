module

public import NearlyMinimax.SpatialSubsetEnergy
public import NearlyMinimax.CardinalInterpolationBias


@[expose] public section

/-! The actual full-design interpolation-weight deficit and its L² bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def cardinalWeightDefect {d n : ℕ} (i : Fin n) (lam T : ℝ)
    (U : Fin n → Covariate d) : ℝ := 1 - integratedCardinalWeight lam T U i

def cardinalDefectSquareBudget (d n : ℕ) (T : ℝ) : ℝ :=
  (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
    T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2)

theorem cardinalWeightDefect_measurable {d n : ℕ} (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) : Measurable (cardinalWeightDefect (d := d) i lam T) :=
  measurable_const.sub (integrated_cardinal_weight_continuous i lam hT).measurable

theorem cardinalWeightDefect_mem_unit {d n : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) (T : ℝ) (U : Fin n → Covariate d) :
    cardinalWeightDefect i lam T U ∈ Icc (0 : ℝ) 1 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam U
  unfold cardinalWeightDefect
  constructor <;> linarith only [h.1, h.2]

theorem cardinalWeightDefect_square_integrable {d n : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun U => cardinalWeightDefect i lam T U ^ 2) (fullSpatialPatchDesign d n) := by
  apply Integrable.of_bound ((cardinalWeightDefect_measurable i lam hT).pow_const 2).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    have h := cardinalWeightDefect_mem_unit i hlam T U
    nlinarith only [h.1, h.2])

theorem cardinalWeightDefect_joint_square_integrable {d n : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalDefect i lam T z.1 z.2 ^ 2)
      ((volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) := by
  have hp := (cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm
  exact hp.integrable_comp_of_integrable (cardinalWeightDefect_square_integrable i hlam hT)

theorem cardinalWeightDefect_full_square_integral_le {d n : ℕ} (hd : 0 < d)
    (hn : 2 ≤ n) (i : Fin n) {T : ℝ} (hT : 1 ≤ T) :
    (∫ U, cardinalWeightDefect i (spatialInterpolationLambda d) T U ^ 2
      ∂fullSpatialPatchDesign d n) ≤ (2 : ℝ) ^ d * cardinalDefectSquareBudget d n T := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hj := cardinalWeightDefect_joint_square_integrable (d := d) i hlam hT
  rw [fullSpatialPatchDesign_split i _]
  change (∫ z : Covariate d × (SpatialScaleIndex i → Covariate d),
    anchoredCardinalDefect i (spatialInterpolationLambda d) T z.1 z.2 ^ 2
      ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) ≤ _
  rw [integral_prod _ hj]
  have hb : (fun x => ∫ Y, anchoredCardinalDefect i (spatialInterpolationLambda d) T x Y ^ 2
      ∂spatialPatchDesignMeasure i d) ≤ᵐ[volume.restrict (spatialPatchBox d)]
      (fun _ => cardinalDefectSquareBudget d n T) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact anchored_cardinal_defect_square_integral_le hd hn i x hx hT
  apply (integral_mono_ae hj.integral_prod_left (integrable_const _) hb).trans_eq
  simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  change volume.real (spatialPatchBox d) * cardinalDefectSquareBudget d n T = _
  rw [spatialPatchBox_real_volume]

theorem cardinalWeightDefect_sum_square_integral_le {d n : ℕ} (hd : 0 < d)
    (hn : 2 ≤ n) {T : ℝ} (hT : 1 ≤ T) :
    (∫ U, (∑ i : Fin n, cardinalWeightDefect i (spatialInterpolationLambda d) T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      (n : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalDefectSquareBudget d n T := by
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d n) Finset.univ
    (fun i => cardinalWeightDefect i (spatialInterpolationLambda d) T)
    ((2 : ℝ) ^ d * cardinalDefectSquareBudget d n T)
    (fun i _ => cardinalWeightDefect_measurable i _ hT)
    (fun i _ => cardinalWeightDefect_square_integrable i
      (by unfold spatialInterpolationLambda; positivity) hT)
    (fun i _ => cardinalWeightDefect_full_square_integral_le hd hn i hT)
  simpa only [Finset.card_univ, Fintype.card_fin, ← mul_assoc] using h

end NearlyMinimax
