module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.FinePairCountTwoSpatialEnergy
public import NearlyMinimax.ResponseConfigurationEnergy


@[expose] public section

/-! Universal deterministic spatial envelopes for the actual signed
response numerators. These depend only on the local chart and fixed caps. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 def cardinalGeometryEnvelope {d n F : ℕ} (q : ℕ) (bd C a ρ η T : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n * (2*cardinalRawAliasCoefficient n bd a η^2 *
    (∑ i, cardinalWeightDefect i (spatialInterpolationLambda d) T U)^2 +
    2*cardinalRawTaylorCoefficient n q bd C a ρ η^2 *
      spatialMatrixL1 (integratedCardinalMatrix (D := F) (spatialInterpolationLambda d) T U)^2)

 theorem cardinalGeometryEnvelope_nonneg {d n F : ℕ} (q : ℕ) (bd C a ρ η T : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ cardinalGeometryEnvelope (F := F) q bd C a ρ η T U := by
  unfold cardinalGeometryEnvelope
  positivity

 theorem cardinalGeometryEnvelope_measurable {d n F : ℕ} (q : ℕ) (bd C a ρ η : ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    Measurable (cardinalGeometryEnvelope (d := d) (n := n) (F := F) q bd C a ρ η T) := by
  unfold cardinalGeometryEnvelope spatialMatrixL1
  have hZ := Finset.measurable_sum (Finset.univ : Finset (Fin n))
    (fun i _ => cardinalWeightDefect_measurable (d := d) i (spatialInterpolationLambda d) hT)
  have hE := Finset.measurable_sum (Finset.univ : Finset (HighFrameIndex d F))
    (fun γ _ => Finset.measurable_sum (Finset.univ : Finset (HighFrameIndex d F))
      (fun δ _ => (integrated_cardinal_matrix_continuous (n := n) (spatialInterpolationLambda d) hT γ δ).measurable.abs))
  exact (((hZ.pow_const 2).const_mul _).add ((hE.pow_const 2).const_mul _)).const_mul _

 theorem cardinalGeometryEnvelope_integrable_and_le {d n F : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (q : ℕ) (bd C a ρ η : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (cardinalGeometryEnvelope (d := d) (n := n) (F := F) q bd C a ρ η T)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, cardinalGeometryEnvelope (F := F) q bd C a ρ η T U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n * cardinalRawSpatialEnergyBudget d n q bd C a ρ η T := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hZ : Integrable (fun U => (∑ i : Fin n, cardinalWeightDefect i (spatialInterpolationLambda d) T U)^2)
      (fullSpatialPatchDesign d n) := by
    have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) Finset.univ
      (fun i U => cardinalWeightDefect i (spatialInterpolationLambda d) T U)
      (fun i _ => cardinalWeightDefect_measurable i _ hT)
      (fun i _ => cardinalWeightDefect_square_integrable i hlam hT)
    simpa only [abs_of_nonneg (cardinalWeightDefect_mem_unit _ hlam T _).1] using h
  have hE := integratedCardinalMatrix_full_square_integrable (D := F) hd hn hT
  have hi : Integrable (cardinalGeometryEnvelope (d := d) (n := n) (F := F) q bd C a ρ η T)
      (fullSpatialPatchDesign d n) := ((hZ.const_mul _).add (hE.const_mul _)).const_mul _
  refine ⟨hi, ?_⟩
  unfold cardinalGeometryEnvelope
  rw [integral_const_mul, integral_add (hZ.const_mul _) (hE.const_mul _), integral_const_mul, integral_const_mul]
  have h := add_le_add (mul_le_mul_of_nonneg_left (cardinalWeightDefect_sum_square_integral_le (d := d) (n := n) (by omega) hn hT)
    (by positivity : 0 ≤ 2*cardinalRawAliasCoefficient n bd a η^2))
    (mul_le_mul_of_nonneg_left (integratedCardinalMatrix_full_square_integral_le (D := F) hd hn hT)
      (by positivity : 0 ≤ 2*cardinalRawTaylorCoefficient n q bd C a ρ η^2))
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (3 : ℝ)^n)).trans_eq (by
    unfold cardinalRawSpatialEnergyBudget; ring)

 theorem highCardinalRawNumerator_sum_square_le_geometry {d n F : ℕ}
    (ad bd : ℝ) (haD : 0 < ad) (hab : ad < bd) {T : ℝ} (hT : 1 ≤ T)
    (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, highCardinalRawNumerator ad bd (spatialInterpolationLambda d) T m D q
      C a V η U p g w c y^2) ≤ cardinalGeometryEnvelope (F := F) q bd C a ρ η T U := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ =>
    highCardinalRawNumerator_square_bound_of_chart ad bd _ haD hab hlam hT m D q hn hnm hnD hnF hq
      C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y)
  exact h.trans_eq (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]; rfl)

 def fineFieldGeometryEnvelope {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n * (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2))^2 *
      (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card),
        |finePairTimeSubsetMoment T0 N U S|)^2

 def finePairAliasGeometryEnvelope {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n * (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2))^2 *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, |finePairTimeSubsetMoment T0 N U S|)^2

 theorem fineFieldGeometryEnvelope_nonneg {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  unfold fineFieldGeometryEnvelope; positivity

 theorem finePairAliasGeometryEnvelope_nonneg {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  unfold finePairAliasGeometryEnvelope; positivity

 theorem fineFieldGeometryEnvelope_measurable {d n : ℕ} [NeZero d] (ad bd T0 N : ℝ)
    (M q : ℕ) (C a ρ η : ℝ) : Measurable (fineFieldGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) := by
  unfold fineFieldGeometryEnvelope
  exact ((Finset.measurable_sum _ (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)).pow_const 2).const_mul _

 theorem finePairAliasGeometryEnvelope_measurable {d n : ℕ} [NeZero d] (ad bd T0 N : ℝ)
    (M q : ℕ) (C a ρ η : ℝ) : Measurable (finePairAliasGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) := by
  unfold finePairAliasGeometryEnvelope
  exact ((Finset.measurable_sum _ (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)).pow_const 2).const_mul _

 theorem fineFieldGeometryEnvelope_integrable_and_le {d n : ℕ} [NeZero d] (hd : 3 ≤ d)
    (ad bd T0 N : ℝ) (hT0 : 0 < T0) (M q : ℕ) (C a ρ η : ℝ) :
    Integrable (fineFieldGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n*finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card)
  have hs (S) (hS : S ∈ s) : 4 ≤ S.card := (Finset.mem_filter.mp hS).2.1
  have hi := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) s
    (fun S U => finePairTimeSubsetMoment T0 N U S)
    (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
    (fun S hS => finePairTimeSubsetMoment_square_integrable hd hT0 S (hs S hS))
  refine ⟨hi.const_mul _, ?_⟩
  unfold fineFieldGeometryEnvelope
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (finePairTimeSubsetMoment_sum_abs_square_integral_le hd (hi := N) hT0 s hs)
    (by positivity : 0 ≤ (3 : ℝ)^n*(finePairDensityCoefficientBudget ad bd M n *
      (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2))^2)
  exact h.trans_eq (by unfold finePairEvenActionSpatialBudget; ring)

 theorem finePairAliasGeometryEnvelope_integrable_and_le {d n : ℕ} [NeZero d] (hd : 4 < d)
    (ad bd T0 N : ℝ) (hT0 : 0 < T0) (hN : T0 ≤ N) (M q : ℕ) (C a ρ η : ℝ) :
    Integrable (finePairAliasGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n*finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hs (S) (hS : S ∈ s) : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
  have hi := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) s
    (fun S U => finePairTimeSubsetMoment T0 N U S)
    (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
    (fun S hS => (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
  refine ⟨hi.const_mul _, ?_⟩
  unfold finePairAliasGeometryEnvelope
  rw [integral_const_mul]
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d n) s
    (fun S U => |finePairTimeSubsetMoment T0 N U S|)
    ((2 : ℝ)^(d*(n-2))*(6*(2 : ℝ)^d*spatialInverseFourConstant d/T0^(d-4)))
    (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)
    (fun S hS => by simpa only [sq_abs] using (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
    (fun S hS => by simpa only [sq_abs] using (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).2)
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (3 : ℝ)^n*(finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2))^2)).trans_eq (by
      dsimp [s]
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      unfold finePairAliasActionSpatialBudget
      ring)

theorem finePairPairAliasAction_sum_square_le_geometry {d n F : ℕ}
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    (∑ y : Fin n → Fin 3, finePairPairAliasAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2) ≤
        finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  let K := finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2)
  let s := (Finset.univ : Finset (Fin n)).powersetCard 2
  let Z := ∑ S ∈ s, |finePairTimeSubsetMoment T0 N U S|
  have hy (y : Fin n → Fin 3) : finePairPairAliasAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2 ≤ K^2*Z^2 := by
    have h := finePairPairAliasAction_abs_bound_of_chart ad bd T0 N haD hab M q hn C a V η ρ hC ha hη hρ hηρ
      U hU p g w hpD c y hc hg hw hp
    have he : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if S.card = 2 then |finePairTimeSubsetMoment T0 N U S| else 0) = Z := by
      dsimp [Z, s]
      rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
    rw [he] at h
    change |_| ≤ K*Z at h
    simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hy y)
  exact h.trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    unfold finePairAliasGeometryEnvelope
    dsimp [K, Z, s]
    ring)

theorem finePairEvenFieldAction_sum_square_le_geometry {d n F : ℕ}
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    (∑ y : Fin n → Fin 3, finePairEvenFieldAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2) ≤
        fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  let K := finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2)
  let s := ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card)
  let Z := ∑ S ∈ s, |finePairTimeSubsetMoment T0 N U S|
  have hy (y : Fin n → Fin 3) : finePairEvenFieldAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2 ≤ K^2*Z^2 := by
    have h := finePairEvenFieldAction_abs_bound_of_chart ad bd T0 N haD hab M q hn C a V η ρ hC ha hη hρ hηρ
      U hU p g w hpD c y hc hg hw hp
    have he : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if 4 ≤ S.card ∧ Even S.card then |finePairTimeSubsetMoment T0 N U S| else 0) = Z := by
      dsimp [Z, s]
      rw [Finset.sum_filter]
    rw [he] at h
    change |_| ≤ K*Z at h
    simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hy y)
  exact h.trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    unfold fineFieldGeometryEnvelope
    dsimp [K, Z, s]
    ring)

 def finePairCountTwoGeometryEnvelope {d : ℕ} (bd a ρ η N : ℝ) (U : Fin 2 → Covariate d) : ℝ :=
  9*(η^2*bd^2*((2*ρ+a)/a^2)^2)^2*finePairDistanceFactor N (U 0) (U 1)^2

 theorem finePairCountTwoGeometryEnvelope_nonneg {d : ℕ} (bd a ρ η N : ℝ)
    (U : Fin 2 → Covariate d) : 0 ≤ finePairCountTwoGeometryEnvelope bd a ρ η N U := by
  unfold finePairCountTwoGeometryEnvelope; positivity

 theorem finePairCountTwoGeometryEnvelope_measurable {d : ℕ} (bd a ρ η N : ℝ) :
    Measurable (finePairCountTwoGeometryEnvelope (d := d) bd a ρ η N) := by
  have hXY : Measurable (fun U : Fin 2 → Covariate d => (U 0, U 1)) :=
    (measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2))
  have hdist : Measurable (fun U : Fin 2 → Covariate d => exactEuclideanDistance (U 0) (U 1)) :=
    exactEuclideanDistance_continuous.measurable.comp hXY
  unfold finePairCountTwoGeometryEnvelope finePairDistanceFactor
  exact (((measurable_const.add (hdist.const_mul N)).mul ((hdist.const_mul N).neg.exp)).pow_const 2).const_mul _

 theorem finePairCountTwoGeometryEnvelope_integrable_and_le {d : ℕ} (hd : 0 < d)
    (bd a ρ η : ℝ) {N : ℝ} (hN : 0 < N) :
    Integrable (finePairCountTwoGeometryEnvelope (d := d) bd a ρ η N) (fullSpatialPatchDesign d 2) ∧
    (∫ U, finePairCountTwoGeometryEnvelope bd a ρ η N U ∂fullSpatialPatchDesign d 2) ≤
      9*finePairCountTwoSpatialBudget d bd a ρ η N := by
  have hp := measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))
  have hi : Integrable (fun U : Fin 2 → Covariate d => finePairDistanceFactor N (U 0) (U 1)^2)
      (fullSpatialPatchDesign d 2) := hp.integrable_comp_of_integrable (finePairDistanceFactor_square_integrable hN)
  refine ⟨hi.const_mul _, ?_⟩
  unfold finePairCountTwoGeometryEnvelope
  rw [integral_const_mul]
  have hInt : (∫ U : Fin 2 → Covariate d, finePairDistanceFactor N (U 0) (U 1)^2 ∂fullSpatialPatchDesign d 2) ≤
      6*(2 : ℝ)^d*spatialExponentialConstant d/N^d :=
    (hp.integral_comp (MeasurableEquiv.finTwoArrow : (Fin 2 → Covariate d) ≃ᵐ (Covariate d × Covariate d)).measurableEmbedding _).trans_le
      (finePairDistanceFactor_square_integral_le hd hN)
  exact (mul_le_mul_of_nonneg_left hInt (by positivity : 0 ≤ 9*(η^2*bd^2*((2*ρ+a)/a^2)^2)^2)).trans_eq
    (by unfold finePairCountTwoSpatialBudget; ring)
theorem finePairCountTwoRawNumerator_sum_square_le_geometry {d F : ℕ} [NeZero d] (hF : 3 ≤ F)
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η ρ : ℝ) (hC : C ≠ 0) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p g w : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ)
    (hf : ∀ i, |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ) :
    (∑ y : Fin 2 → Fin 3, (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y)^2) ≤
      finePairCountTwoGeometryEnvelope bd a ρ η N U :=
    finePairCountTwoRawNumerator_sum_square_le hF ad bd T0 N haD hab hT0 hN D M q hD hM hq
      C a V η ρ hC ha hρ U hU p g w hp hw c hf

end NearlyMinimax
