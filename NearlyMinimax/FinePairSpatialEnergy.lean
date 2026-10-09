module

public import NearlyMinimax.FinePairActionEnvelopes
public import NearlyMinimax.FineFieldSumEnergy


@[expose] public section

/-! Genuine spatial energy of the higher even-field action. All moment
bounds here concern the actual time-integrated hyperplane field law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 theorem highFrameFeature_spatial_measurable {d n F : ℕ} (i : Fin n)
    (γ : HighFrameIndex d F) :
    Measurable (fun U : Fin n → Covariate d => highFrameFeature (U i) γ) := by
  unfold highFrameFeature
  exact Finset.measurable_prod _ (fun r _ =>
    (((measurable_pi_apply r).comp (measurable_pi_apply i)).div_const 8).pow_const _)

 theorem highResponseProduct_spatial_measurable {d n F : ℕ} (a V η : ℝ)
    (g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun U => g U i)) (hw : ∀ i, Measurable (fun U => w U i))
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun U => highResponseProduct a V η (g U) (w U)
      (fun i => highFrameFeature (U i)) c y) := by
  unfold highResponseProduct
  apply Finset.measurable_prod
  intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  exact (hg i).add ((measurable_const.mul (hw i)).mul
    (Finset.measurable_sum _ (fun γ _ => (highFrameFeature_spatial_measurable i γ).mul_const _)))

 theorem finePairResponseAction_spatial_measurable {d n F : ℕ} (q : ℕ) (C a V η : ℝ)
    (g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun U => g U i)) (hw : ∀ i, Measurable (fun U => w U i))
    (A : HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun U => responseMatrixAction q C A c (fun v =>
      highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)) := by
  simp_rw [← highResponseMark_action]
  exact Finset.measurable_sum _ (fun h _ =>
    (highResponseProduct_spatial_measurable a V η g w hg hw _ y).const_mul _)

 theorem finePairEvenFieldAction_spatial_measurable {d n F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (M q : ℕ) (C a V η : ℝ)
    (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hp : ∀ i, Measurable (fun U => p U i)) (hg : ∀ i, Measurable (fun U => g U i))
    (hw : ∀ i, Measurable (fun U => w U i))
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun U => finePairEvenFieldAction ad bd T0 N M q C U (p U) c
      (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)) := by
  unfold finePairEvenFieldAction
  apply Finset.measurable_sum
  intro S hS
  exact ((((Finset.measurable_prod S (fun i _ => hp i)).const_mul _).mul_const _).mul
    (finePairTimeSubsetMoment_measurable T0 N S)).mul
      (finePairResponseAction_spatial_measurable q C a V η g w hg hw _ c y)

 theorem fullSpatialPatchDesign_ae_coordinate_bound {d n : ℕ} :
    ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i r, |U i r| ≤ 2 := by
  have hU : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, U i ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => volume.restrict (spatialPatchBox d))
      (i := i)).eventually (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hU] with U hU i r
  exact (abs_le.mpr ⟨(hU i).1 r, (hU i).2 r⟩).trans (by norm_num)

 theorem finite_sum_abs_square_integrable {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ) :
    Integrable (fun x => (∑ i ∈ s, |f i x|)^2) μ := by
  have hupper : Integrable (fun x => (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2) μ :=
    (integrable_finsetSum s hi).const_mul _
  apply hupper.mono' ((Finset.measurable_sum s (fun i hi => (hm i hi).abs)).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_sq]
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : I => (1 : ℝ)) (fun i => |f i x|))

 def finePairEvenActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2))^2 *
      fineFieldSubsetEnergyBase d ^ n * (n : ℝ)^8 * (T0 ^ (2-(d : ℝ)))^2

 theorem finePairEvenFieldAction_spatial_square_integrable_and_le {d n F : ℕ} [NeZero d]
    (hd : 3 ≤ d) (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 < T0)
    (M q : ℕ) (hn : 1 ≤ n) (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
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
    Integrable (fun U => finePairEvenFieldAction ad bd T0 N M q C U (p U) c
      (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)^2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, finePairEvenFieldAction ad bd T0 N M q C U (p U) c
      (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)^2
      ∂fullSpatialPatchDesign d n) ≤ finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card)
  let K := finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2)
  let R := fun U => finePairEvenFieldAction ad bd T0 N M q C U (p U) c
    (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)
  let H := fun U : Fin n → Covariate d => ∑ S ∈ s, |finePairTimeSubsetMoment T0 N U S|
  have hs (S) (hS : S ∈ s) : 4 ≤ S.card := (Finset.mem_filter.mp hS).2.1
  have hH : Integrable (fun U => H U ^ 2) (fullSpatialPatchDesign d n) :=
    finite_sum_abs_square_integrable _ s _
      (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
      (fun S hS => finePairTimeSubsetMoment_square_integrable hd hT0 S (hs S hS))
  have hRmeas : Measurable R := finePairEvenFieldAction_spatial_measurable ad bd T0 N M q C a V η
    p g w hpmeas hgmeas hwmeas c y
  have hbound : ∀ᵐ U ∂fullSpatialPatchDesign d n, R U ^ 2 ≤ K^2 * H U ^ 2 := by
    filter_upwards [fullSpatialPatchDesign_ae_coordinate_bound, hpD, hg, hw] with U hU hpU hgU hwU
    have h := finePairEvenFieldAction_abs_bound_of_chart ad bd T0 N haD hab M q hn C a V η ρ
      hC ha hη hρ hηρ U hU (p U) (g U) (w U) hpU c y hc hgU hwU hp
    have he : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if 4 ≤ S.card ∧ Even S.card then |finePairTimeSubsetMoment T0 N U S| else 0) = H U := by
      dsimp [H, s]
      rw [Finset.sum_filter]
    rw [he] at h
    change |R U| ≤ K * H U at h
    have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
    simpa only [sq_abs, mul_pow] using hsq
  have hupper : Integrable (fun U => K^2 * H U ^ 2) (fullSpatialPatchDesign d n) := hH.const_mul _
  have hR : Integrable (fun U => R U ^ 2) (fullSpatialPatchDesign d n) :=
    hupper.mono' (hRmeas.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hbound] with U hU
      simpa only [Real.norm_eq_abs, abs_sq] using hU)
  refine ⟨hR, (integral_mono_ae hR hupper hbound).trans ?_⟩
  rw [integral_const_mul]
  have hsum := finePairTimeSubsetMoment_sum_abs_square_integral_le hd (hi := N) hT0 s hs
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg K)).trans_eq (by
    dsimp [H, K, finePairEvenActionSpatialBudget]; ring)

end NearlyMinimax
