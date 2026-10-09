module

public import NearlyMinimax.FinePairSpatialEnergy
public import NearlyMinimax.SpatialFineAliasPairL2


@[expose] public section

/-! The actual card-two fine-field alias is the Laplace kernel Wfi.
Its selected-subset spatial energy includes the exact unused-volume factor. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 theorem fullSpatialPatchDesign_ae_hyperplaneCube {d n : ℕ} :
    ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, U i ∈ hyperplaneCube d := by
  have hU : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, U i ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => volume.restrict (spatialPatchBox d))
      (i := i)).eventually (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hU] with U hU i r
  exact abs_le.mpr ⟨(hU i).1 r, (hU i).2 r⟩

 theorem finePairTimeSubsetMoment_univ_pair {d : ℕ} [NeZero d] {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : lo ≤ hi) (U : Fin 2 → Covariate d)
    (hU : ∀ i, U i ∈ hyperplaneCube d) :
    finePairTimeSubsetMoment lo hi U Finset.univ =
      fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) := by
  unfold finePairTimeSubsetMoment
  simp only [Fin.prod_univ_two]
  rw [finePairTimeFieldValue_weighted_covariance d lo hi hlo _ _ (hU 0) (hU 1)]
  rw [exactEuclideanDistance_eq_euclideanNorm]
  unfold fineAliasLaplaceKernel
  rw [intervalIntegral.integral_of_le hhi, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun T => by dsimp; rw [neg_mul])

 theorem finePairTimeSubsetMoment_pair_square_integrable_and_le {d j : ℕ} [NeZero d]
    (hd : 4 < d) {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi) (hj : j = 2) :
    Integrable (fun U : Fin j → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2)
      (fullSpatialPatchDesign d j) ∧
    (∫ U : Fin j → Covariate d, finePairTimeSubsetMoment lo hi U Finset.univ ^ 2
      ∂fullSpatialPatchDesign d j) ≤ 6 * (2 : ℝ)^d * spatialInverseFourConstant d / lo^(d-4) := by
  subst j
  have he : (fun U : Fin 2 → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) =ᵐ[fullSpatialPatchDesign d 2]
      (fun U => fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) ^ 2) := by
    filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
    rw [finePairTimeSubsetMoment_univ_pair hlo.le hhi U hU]
  have h := fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le hd hlo hhi
  refine ⟨h.1.congr he.symm, ?_⟩
  exact (integral_congr_ae he).trans_le h.2

 theorem finePairTimeSubsetMoment_two_subset_square_integrable_and_le {d n : ℕ} [NeZero d]
    (hd : 4 < d) {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (S : Finset (Fin n)) (hS : S.card = 2) :
    Integrable (fun U : Fin n → Covariate d => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U : Fin n → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      (2 : ℝ)^(d*(n-2)) * (6*(2 : ℝ)^d*spatialInverseFourConstant d / lo^(d-4)) := by
  have h := finePairTimeSubsetMoment_pair_square_integrable_and_le hd hlo hhi hS
  refine ⟨?_, ?_⟩
  · simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
    exact spatial_subset_square_integrable_enumerated S _ h.1
  · rw [finePairTimeSubsetMoment_square_integral_reindex]
    have hb := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (2 : ℝ)^(d*(n-S.card)))
    simpa only [hS] using hb

 theorem finePairPairAliasAction_spatial_measurable {d n F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (M q : ℕ) (C a V η : ℝ)
    (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hp : ∀ i, Measurable (fun U => p U i)) (hg : ∀ i, Measurable (fun U => g U i))
    (hw : ∀ i, Measurable (fun U => w U i))
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun U => finePairPairAliasAction ad bd T0 N M q C U (p U) c
      (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)) := by
  unfold finePairPairAliasAction
  apply Finset.measurable_sum
  intro S hS
  exact ((((Finset.measurable_prod S (fun i _ => hp i)).const_mul _).mul_const _).mul
    (finePairTimeSubsetMoment_measurable T0 N S)).mul
      (finePairResponseAction_spatial_measurable q C a V η g w hg hw _ c y)

 def finePairAliasActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2))^2 *
      (n.choose 2 : ℝ)^2 * (2 : ℝ)^(d*(n-2)) *
        (6*(2 : ℝ)^d*spatialInverseFourConstant d / T0^(d-4))

 theorem finePairPairAliasAction_spatial_square_integrable_and_le {d n F : ℕ} [NeZero d]
    (hd : 4 < d) (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd)
    (hT0 : 0 < T0) (hN : T0 ≤ N) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hpmeas : ∀ i, Measurable (fun U => p U i))
    (hgmeas : ∀ i, Measurable (fun U => g U i))
    (hwmeas : ∀ i, Measurable (fun U => w U i))
    (hpD : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, p U i ∈ Icc ad bd)
    (hg : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |g U i| ≤ ρ/2)
    (hw : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |w U i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    Integrable (fun U => finePairPairAliasAction ad bd T0 N M q C U (p U) c
      (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)^2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, finePairPairAliasAction ad bd T0 N M q C U (p U) c
      (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)^2
      ∂fullSpatialPatchDesign d n) ≤ finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := (Finset.univ : Finset (Fin n)).powersetCard 2
  let K := finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2)
  let R := fun U => finePairPairAliasAction ad bd T0 N M q C U (p U) c
    (fun v => highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)
  let H := fun U : Fin n → Covariate d => ∑ S ∈ s, |finePairTimeSubsetMoment T0 N U S|
  have hs (S) (hS : S ∈ s) : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
  have hH : Integrable (fun U => H U ^ 2) (fullSpatialPatchDesign d n) :=
    finite_sum_abs_square_integrable _ s _
      (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
      (fun S hS => (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
  have hRmeas : Measurable R := finePairPairAliasAction_spatial_measurable ad bd T0 N M q C a V η
    p g w hpmeas hgmeas hwmeas c y
  have hbound : ∀ᵐ U ∂fullSpatialPatchDesign d n, R U ^ 2 ≤ K^2 * H U ^ 2 := by
    filter_upwards [fullSpatialPatchDesign_ae_coordinate_bound, hpD, hg, hw] with U hU hpU hgU hwU
    have h := finePairPairAliasAction_abs_bound_of_chart ad bd T0 N haD hab M q hn C a V η ρ
      hC ha hη hρ hηρ U hU (p U) (g U) (w U) hpU c y hc hgU hwU hp
    have he : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if S.card = 2 then |finePairTimeSubsetMoment T0 N U S| else 0) = H U := by
      dsimp [H, s]
      rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
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
  have hsum := finite_sum_square_integral_le (fullSpatialPatchDesign d n) s
    (fun S U => |finePairTimeSubsetMoment T0 N U S|)
    ((2 : ℝ)^(d*(n-2)) * (6*(2 : ℝ)^d*spatialInverseFourConstant d / T0^(d-4)))
    (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)
    (fun S hS => by simpa only [sq_abs] using
      (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
    (fun S hS => by simpa only [sq_abs] using
      (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).2)
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg K)).trans_eq (by
    dsimp [s, H, K, finePairAliasActionSpatialBudget]
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    ring)

end NearlyMinimax
