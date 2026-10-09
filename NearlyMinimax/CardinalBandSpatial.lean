module

public import NearlyMinimax.CardinalCoefficientBounds
public import NearlyMinimax.CardinalWeightedBounds
public import NearlyMinimax.CardinalSeparatedBand


@[expose] public section

/-! Actual scale-band spatial integrals used in the interpolation matrix
squared-norm bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def anchoredCardinalScale {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalScale lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i

theorem anchored_cardinal_scale_product_actual {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalScale i lam x t Y = ∏ j : SpatialScaleIndex i,
      t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x (Y j))) := by
  unfold anchoredCardinalScale
  rw [spatial_cardinal_scale_product]
  simp_rw [anchored_configuration_same, anchored_configuration_other]

theorem anchored_cardinal_scale_continuous_actual {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d) :
    Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2) := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialSquaredDistance
  fun_prop

theorem anchored_cardinal_scale_nonnegative_actual {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) (Y : SpatialScaleIndex i → Covariate d) :
    0 ≤ anchoredCardinalScale i lam x t Y :=
  spatial_cardinal_scale_nonnegative i lam (anchoredPatchConfiguration i x Y) t ht

theorem anchored_cardinal_scale_upper_bound {d n : ℕ} (i : Fin n) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 1 ≤ T) (x : Covariate d) (t : SpatialScaleVector i)
    (ht : t ∈ spatialScaleDomain i T) (Y : SpatialScaleIndex i → Covariate d) :
    |anchoredCardinalScale i lam x t Y| ≤ (T ^ 2 * lam ^ 2) ^ Fintype.card (SpatialScaleIndex i) := by
  rw [abs_of_nonneg (anchored_cardinal_scale_nonnegative_actual i lam x t ht.1 Y),
    anchored_cardinal_scale_product_actual]
  calc
    _ ≤ ∏ _j : SpatialScaleIndex i, T ^ 2 * lam ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact mul_nonneg (mul_nonneg (ht.1 j) (sq_nonneg _)) (Real.exp_pos _).le
      · intro j hj
        have htj : 0 ≤ t j := ht.1 j
        have hdist : 0 ≤ spatialSquaredDistance x (Y j) := Finset.sum_nonneg (fun r _ => sq_nonneg _)
        have he : Real.exp (-(t j * lam * spatialSquaredDistance x (Y j))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg htj hlam) hdist))
        have hsmall := (spatial_scale_domain_subset_box i T hT ht).2 j
        exact (mul_le_mul_of_nonneg_left he (mul_nonneg htj (sq_nonneg _))).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_right (show t j ≤ T ^ 2 by linarith) (sq_nonneg lam))
    _ = _ := by simp

theorem anchored_cardinal_band_scale_joint_integrable {d n : ℕ} (i : Fin n) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 1 ≤ T) (L : ℝ) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2)
      ((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod (spatialPatchDesignMeasure i d)) := by
  letI := spatial_scale_measure_finite i T hT
  have hμ : volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L) ≤ spatialScaleMeasure i T :=
    Measure.restrict_mono_set volume Set.diff_subset
  letI : IsFiniteMeasure (volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)) :=
    isFiniteMeasure_of_le (spatialScaleMeasure i T) hμ
  apply Integrable.of_bound (anchored_cardinal_scale_continuous_actual i lam x).aestronglyMeasurable
    ((T ^ 2 * lam ^ 2) ^ Fintype.card (SpatialScaleIndex i))
  have hae : ∀ᵐ z ∂((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod
      (spatialPatchDesignMeasure i d)), z.1 ∈ spatialScaleDomain i T := by
    apply (Measure.ae_prod_iff_ae_ae ((spatial_scale_domain_isClosed i T).measurableSet.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    exact ae_of_all _ (fun Y => ht.1)
  filter_upwards [hae] with z hz
  rw [Real.norm_eq_abs]
  exact anchored_cardinal_scale_upper_bound i hlam hT x z.1 hz z.2

def spatialScaleIntegralConstant (d : ℕ) : ℝ :=
  (spatialInterpolationLambda d) ^ 2 * Real.exp (1 / 2) *
    (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d

theorem anchored_cardinal_scale_spatial_integrable {d n : ℕ} (i : Fin n) (lam : ℝ)
    (x : Covariate d) (t : SpatialScaleVector i) :
    Integrable (fun Y => anchoredCardinalScale i lam x t Y) (spatialPatchDesignMeasure i d) := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialPatchDesignMeasure
  apply Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (j : SpatialScaleIndex i) (y : Covariate d) =>
      t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x y)))
  intro j
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  unfold spatialSquaredDistance
  fun_prop

theorem anchored_cardinal_scale_spatial_integral_product {d n : ℕ} (i : Fin n) (lam : ℝ)
    (x : Covariate d) (t : SpatialScaleVector i) :
    (∫ Y, anchoredCardinalScale i lam x t Y ∂spatialPatchDesignMeasure i d) =
      ∏ j : SpatialScaleIndex i, lam ^ 2 * ∫ y in spatialPatchBox d,
        t j * Real.exp (-(t j * lam * spatialSquaredDistance x y)) := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialPatchDesignMeasure
  rw [integral_fintype_prod_eq_prod
    (fun (j : SpatialScaleIndex i) (y : Covariate d) =>
      t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x y)))]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem anchored_cardinal_scale_spatial_integral_decay {d n : ℕ} (hd : 0 < d) (i : Fin n)
    (x : Covariate d) (hx : x ∈ spatialPatchBox d) (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    (∫ Y, anchoredCardinalScale i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤
      (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (1 - (d : ℝ) / 2) := by
  rw [anchored_cardinal_scale_spatial_integral_product]
  have h : (∏ j : SpatialScaleIndex i, (spatialInterpolationLambda d) ^ 2 *
      ∫ y in spatialPatchBox d, t j * Real.exp (-(t j * spatialInterpolationLambda d * spatialSquaredDistance x y))) ≤
      ∏ j : SpatialScaleIndex i, spatialScaleIntegralConstant d * (1 + t j) ^ (1 - (d : ℝ) / 2) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      apply mul_nonneg (sq_nonneg _)
      apply integral_nonneg
      intro y
      exact mul_nonneg (ht j) (Real.exp_pos _).le
    · intro j hj
      have hdec := mul_le_mul_of_nonneg_left
        (spatial_scale_exponential_patch_integral_decay hd (t j) (ht j) x hx)
        (sq_nonneg (spatialInterpolationLambda d))
      simpa only [spatialScaleIntegralConstant, mul_assoc] using hdec
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

/-- The actual squared-kernel spatial decay integrated over a true
truncated scale band, with every Fubini exchange justified. -/
theorem anchored_cardinal_band_scale_spatial_integral_bound {d n : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) :
    (∫ Y, (∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
      anchoredCardinalScale i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialScaleIntegralConstant d) ^ (n - 1) *
        L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2) := by
  have hd0 : 0 < d := by omega
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  let b : ℝ := ((d : ℝ) - 4) / 2
  have hb : (1 / 2 : ℝ) ≤ b := by dsimp [b]; linarith
  have hpos : 0 < b := by linarith
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hjoint := anchored_cardinal_band_scale_joint_integrable i hlam hT L x
  have hfub :
      (∫ Y, (∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
        anchoredCardinalScale i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d) =
        ∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
          (∫ Y, anchoredCardinalScale i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) :=
    (integral_prod_symm _ hjoint).symm.trans (integral_prod _ hjoint)
  rw [hfub]
  have hsub : spatialScaleDomain i T \ spatialScaleDomain i L ⊆ Ici 0 \ spatialScaleDomain i L :=
    fun t ht => ⟨ht.1.1, ht.2⟩
  have hμ := Measure.restrict_mono_set (volume : Measure (SpatialScaleVector i)) hsub
  have hpowint := spatial_scale_complement_power_integrable hn i hpos L
  have hpowint' : Integrable (fun t : SpatialScaleVector i => ∏ j, (1 + t j) ^ (-b - 1 : ℝ))
      (volume.restrict (Ici 0 \ spatialScaleDomain i L)) := hpowint
  have hpowband := hpowint'.mono_measure hμ
  have hdom : (fun t : SpatialScaleVector i =>
      ∫ Y, anchoredCardinalScale i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤ᵐ[
        volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)]
      (fun t => (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) := by
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    have h := anchored_cardinal_scale_spatial_integral_decay hd0 i x hx t ht.1.1
    simpa only [show 1 - (d : ℝ) / 2 = -b - 1 by dsimp [b]; ring] using h
  have hnn : ∀ᵐ t ∂volume.restrict (Ici 0 \ spatialScaleDomain i L),
      0 ≤ ∏ j : SpatialScaleIndex i, (1 + t j) ^ (-b - 1 : ℝ) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    apply Finset.prod_nonneg
    intro j hj
    exact Real.rpow_nonneg (by have htj : (0 : ℝ) ≤ t j := ht.1 j; linarith) _
  have hC : 0 ≤ (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) := by
    unfold spatialScaleIntegralConstant
    positivity
  have hfirst := integral_mono_ae hjoint.integral_prod_left (hpowband.const_mul _) hdom
  rw [integral_const_mul] at hfirst
  have hmiddle := integral_mono_measure hμ hnn hpowint
  have htail := spatial_scale_complement_power_integral_le hn i hb hL
  have hfull := hfirst.trans ((mul_le_mul_of_nonneg_left hmiddle hC).trans (mul_le_mul_of_nonneg_left htail hC))
  rw [spatial_scale_index_card, show -2 * b = 4 - (d : ℝ) by dsimp [b]; ring] at hfull
  simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hfull

end NearlyMinimax
