module

public import NearlyMinimax.SpatialLaplaceTail
public import NearlyMinimax.CardinalProductDesign


@[expose] public section

/-! Genuine bounded-domain pair integration of the actual fine-alias
Laplace kernel, including the real Fin2 product coordinate law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- A nonnegative whole-space kernel with a uniform true section bound has
an actual finite-domain product integral bound. -/
theorem finite_pair_kernel_integrable_and_integral_le {X : Type*}
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ ≤ ν) (f : X × X → ℝ) (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) (K : ℝ)
    (hi : ∀ x, Integrable (fun y => f (x,y)) ν)
    (hb : ∀ x, (∫ y, f (x,y) ∂ν) ≤ K) :
    Integrable f (μ.prod μ) ∧ (∫ z, f z ∂μ.prod μ) ≤ μ.real univ * K := by
  have hsection (x : X) : Integrable (fun y => f (x,y)) μ := (hi x).mono_measure hμ
  have hsectionBound (x : X) : (∫ y, f (x,y) ∂μ) ≤ K :=
    (integral_mono_measure hμ (Filter.Eventually.of_forall fun y => hn (x,y)) (hi x)).trans (hb x)
  have hinner : Integrable (fun x => ∫ y, ‖f (x,y)‖ ∂μ) μ := by
    have hmin : AEStronglyMeasurable (fun x => ∫ y, ‖f (x,y)‖ ∂μ) μ :=
      hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    apply (integrable_const K).mono' hmin
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact hsectionBound x
  have hf : Integrable f (μ.prod μ) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hinner⟩
  refine ⟨hf, ?_⟩
  rw [integral_prod _ hf]
  simpa only [integral_const, smul_eq_mul] using
    integral_mono hf.integral_prod_left (integrable_const K) hsectionBound

/-- Actual Wfi² integration over the two source cube points. -/
theorem fineAlias_spatial_pair_squared_integrable_and_integral_le {d : ℕ} (hd : 4 < d)
    {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N) :
    Integrable (fun xy : Covariate d × Covariate d =>
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance xy.1 xy.2))^2)
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ∧
    (∫ xy : Covariate d × Covariate d,
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance xy.1 xy.2))^2
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      6 * (2 : ℝ)^d * spatialInverseFourConstant d / T0^(d-4) := by
  have hm := ((fineAliasLaplaceKernel_measurable T0 N hN).comp
    (exactEuclideanDistance_continuous (d := d)).measurable).pow_const 2
  have h := finite_pair_kernel_integrable_and_integral_le volume (volume.restrict (spatialPatchBox d))
    Measure.restrict_le_self _ hm (fun _ => sq_nonneg _) (6*spatialInverseFourConstant d/T0^(d-4))
    (fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hT0 hN x).1)
    (fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hT0 hN x).2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [measureReal_def, Measure.restrict_apply_univ]
  change volume.real (spatialPatchBox d) * _ = _
  rw [spatialPatchBox_real_volume]
  ring

/-- The same genuine fine-alias estimate in the paper's Fin2 tuple coordinates. -/
theorem fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le {d : ℕ} (hd : 4 < d)
    {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N) :
    Integrable (fun U : Fin 2 → Covariate d =>
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance (U 0) (U 1)))^2)
      (fullSpatialPatchDesign d 2) ∧
    (∫ U : Fin 2 → Covariate d,
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance (U 0) (U 1)))^2
      ∂fullSpatialPatchDesign d 2) ≤
      6 * (2 : ℝ)^d * spatialInverseFourConstant d / T0^(d-4) := by
  have h := fineAlias_spatial_pair_squared_integrable_and_integral_le hd hT0 hN
  have hp := measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))
  refine ⟨?_, ?_⟩
  · exact hp.integrable_comp_of_integrable h.1
  · exact (hp.integral_comp (MeasurableEquiv.finTwoArrow : (Fin 2 → Covariate d) ≃ᵐ (Covariate d × Covariate d)).measurableEmbedding _).trans_le h.2

end NearlyMinimax
