module

public import NearlyMinimax.HighSpatialEnvelopes
public import NearlyMinimax.HigherBandRawCollapse
public import NearlyMinimax.HighSourceHigherCounts
public import NearlyMinimax.OrdinaryFineAliasGeometryEnvelope


@[expose] public section

/-! Actual full higher-count source numerator and a deterministic geometric
square envelope. All signed rows are summed before the one heat correction. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 theorem highCardinalRawNumerator_eq_matrix_heat {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      (∏ i, p i)*responseMatrixAction q C (integratedCardinalMatrix lam T U) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2*(∏ i, p i)*∑ i, (w i)^2*highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
  rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hC U hU p g w hp c y, integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
  ring

 theorem higherBandTargetScale_pos_of_physical {d n D : ℕ} (hn : 3 ≤ n) (hnD : n ≤ D)
    (N μ : ℝ) (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N μ) :
    0 < higherBandTargetScale d n N μ := by
  let j : Fin (D-2) := ⟨n-3, by omega⟩
  have hj : j.val+3 = n := by dsimp [j]; omega
  simpa only [hj] using hnu j

 theorem completeSourceRawNumerator_higher_components {d n : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hℓ : 1 ≤ ℓ)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N μ)
    (hFine : ∀ j : Fin (D-2), ℓ < higherBandTargetScale d (j.val+3) N μ → j.val+3 ≤ M)
    (C a V η : ℝ) (hC : C ≠ 0) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      highCardinalRawNumerator ad bd lam (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y +
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0) +
      (if M<n then finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) := by
  have hnuN := higherBandTargetScale_pos_of_physical hn hnD N μ hnu
  have hmat : integratedCardinalMatrix (D := D) lam (max 1 (higherBandTargetScale d n N μ)) U =
      integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U := by
    funext γ δ
    exact integrated_cardinal_matrix_max_one (by omega) lam hnuN U γ δ
  rw [completeSourceRawNumerator_higher ad bd lam ℓ N μ haD hab D M q hn hnD C a V η U p g w hp c y,
    higherBandFamilyFirstAction_matched_and_full_fine_alias ad bd lam ℓ N μ haD hab hlam hℓ D M q hn hnD hnu hFine
      C a V η U hU p g w hp c y,
    highCardinalRawNumerator_eq_matrix_heat ad bd lam haD hab hlam (le_max_left _ _) D D q (by omega) hnD hnD hnD
      C a V η hC U hU p g w hp c y, hmat]
  by_cases hnM : M<n
  · simp only [if_pos hnM]
    ring
  · rw [if_neg hnM, finePairPairAliasAction_zero_selected_count ad bd ℓ N haD hab M q hn (le_of_not_gt hnM) C U p c]
    simp only [if_neg hnM, ite_self]
    ring

 def completeSourceHigherGeometryEnvelope {d n D : ℕ} (aD bD c0 ℓ N μ : ℝ)
    (M R q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) : ℝ :=
  4*(cardinalGeometryEnvelope (F := D) q (bD-(M : ℝ)⁻¹) C a ρ η (max 1 (higherBandTargetScale d n N μ)) U +
    (if M<n then ordinaryFineAliasFamilyResponseSquareEnvelope (F := D) (ordinaryFineAliasTargetSet d D ℓ N μ)
      M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U else 0) +
    (if M<n then finePairAliasGeometryEnvelope (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U else 0) +
    fineFieldGeometryEnvelope (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U)

 theorem completeSourceHigherGeometryEnvelope_nonneg {d n D : ℕ} (aD bD c0 ℓ N μ : ℝ)
    (M R q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) :
    0 ≤ completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η U := by
  unfold completeSourceHigherGeometryEnvelope
  have hA := cardinalGeometryEnvelope_nonneg (F := D) q (bD-(M : ℝ)⁻¹) C a ρ η (max 1 (higherBandTargetScale d n N μ)) U
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg (F := D) (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U
  have hP := finePairAliasGeometryEnvelope_nonneg (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U
  have hF := fineFieldGeometryEnvelope_nonneg (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U
  split_ifs <;> positivity

 theorem completeSourceRawNumerator_higher_square_le_geometry {d n : ℕ} [NeZero d]
    (aD bD c0 ℓ N μ : ℝ) (haD : 0 < aD) (hℓ : 1 ≤ ℓ) (D M R q : ℕ)
    (hshrink : aD+(M : ℝ)⁻¹ < bD-(M : ℝ)⁻¹) (htau : shrunkDensityExponent aD bD M ≤ c0)
    (hn : 3 ≤ n) (hnD : n ≤ D) (hq : 1 ≤ q)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N μ)
    (hFine : ∀ j : Fin (D-2), ℓ < higherBandTargetScale d (j.val+3) N μ → j.val+3 ≤ M)
    (hI : ∀ r ∈ ordinaryFineAliasTargetSet d D ℓ N μ, 1 ≤ r ∧ r ≤ R)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹))
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1) (c : HighFrameIndex d D → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, completeSourceRawNumerator (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹)
      (spatialInterpolationLambda d) ℓ N μ D M q C a V η U p g w c y^2) ≤
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η U := by
  let ad := aD+(M : ℝ)⁻¹
  let bd := bD-(M : ℝ)⁻¹
  have had : 0 < ad := by dsimp [ad]; positivity
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  let A := fun y => highCardinalRawNumerator ad bd (spatialInterpolationLambda d)
    (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y
  let B := fun y => if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
    ad bd (spatialInterpolationLambda d) ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0
  let P := fun y => if M<n then finePairPairAliasAction ad bd ℓ N M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0
  let F := fun y => finePairEvenFieldAction ad bd ℓ N M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)
  have hA := highCardinalRawNumerator_sum_square_le_geometry (T := max 1 (higherBandTargetScale d n N μ)) ad bd had hshrink (le_max_left _ _) D D q
    (by omega) hnD hnD hnD hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp
  have hB : (∑ y, B y^2) ≤ (if M<n then ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
      (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U else 0) := by
    by_cases hMn : M<n
    · simp only [B, if_pos hMn]
      exact ordinaryFineAliasFamilyResponseSquareEnvelope_dominates _ aD bD c0 ℓ _ haD hshrink htau hI q
        (by omega) C a V η ρ hC ha hη hρ hηρ U hU (fun _ => p) (fun _ => g) (fun _ => w) (fun _ => c)
          (fun _ => hpD) (fun _ => hg) (fun _ => hw) (fun _ => hc) hp
    · simp [B, hMn]
  have hP : (∑ y, P y^2) ≤ (if M<n then finePairAliasGeometryEnvelope ad bd ℓ N M q C a ρ η U else 0) := by
    by_cases hMn : M<n
    · simp only [P, if_pos hMn]
      exact finePairPairAliasAction_sum_square_le_geometry ad bd ℓ N had hshrink M q (by omega) C a V η ρ
        hC ha hη hρ hηρ U hU p g w hpD c hc hg hw hp
    · simp [P, hMn]
  have hF := finePairEvenFieldAction_sum_square_le_geometry ad bd ℓ N had hshrink M q (by omega) C a V η ρ
    hC ha hη hρ hηρ U hU p g w hpD c hc hg hw hp
  have hb (y : Fin n → Fin 3) : completeSourceRawNumerator ad bd (spatialInterpolationLambda d) ℓ N μ
      D M q C a V η U p g w c y^2 ≤ 4*(A y^2+B y^2+P y^2+F y^2) := by
    rw [completeSourceRawNumerator_higher_components ad bd _ ℓ N μ had hshrink hlam hℓ D M q hn hnD
      hnu hFine C a V η (lt_of_lt_of_le zero_lt_one hC).ne' U hU p g w hpD c y]
    change (A y+B y+P y+F y)^2 ≤ _
    nlinarith only [sq_nonneg (A y-B y), sq_nonneg (P y-F y), sq_nonneg (A y+B y-P y-F y)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hb y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  exact h.trans (by
    unfold completeSourceHigherGeometryEnvelope
    convert mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hB) hP) hF)
      (by norm_num : (0 : ℝ) ≤ 4) using 1)

 theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable {d n F : ℕ}
    (hd : 5 ≤ d) (I : Finset ℕ) (M R q : ℕ) (ad bd c0 C a ρ η L : ℝ)
    (T : ℕ → ℝ) (hL : 1 ≤ L) (hI : ∀ r ∈ I, 2 ≤ r ∧ L ≤ T r) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a ρ η L T) (fullSpatialPatchDesign d n) := by
  let f := fun r (U : Fin n → Covariate d) => ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hL (hL.trans (hI r hr).2)).const_mul _
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U^2) (fullSpatialPatchDesign d n) := by
    have h := (ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
      hd (hI r hr).1 hL (hL.trans (hI r hr).2) (hI r hr).2).1.const_mul
        ((ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η)^2)
    convert h using 1
    funext U
    dsimp [f, ordinaryFineAliasGeometryKernel]
    ring
  have hs : Integrable (fun U => (∑ r ∈ I, f r U)^2) (fullSpatialPatchDesign d n) := by
    have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) I f hm hi
    apply h.mono' ((Finset.measurable_sum I hm).pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro U
    have hb := Finset.abs_sum_le_sum_abs (fun r => f r U) I
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr hb
  exact hs.const_mul ((3 : ℝ)^n)

 theorem completeSourceHigherGeometryEnvelope_measurable {d n D : ℕ} [NeZero d]
    (aD bD c0 ℓ N μ : ℝ) (M R q : ℕ) (C a ρ η : ℝ) (hℓ : 1 ≤ ℓ) :
    Measurable (completeSourceHigherGeometryEnvelope (d := d) (n := n) (D := D)
      aD bD c0 ℓ N μ M R q C a ρ η) := by
  have hA := cardinalGeometryEnvelope_measurable (d := d) (n := n) (F := D) q (bD-(M : ℝ)⁻¹) C a ρ η
    (T := max 1 (higherBandTargetScale d n N μ)) (le_max_left _ _)
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_measurable (d := d) (n := n) (F := D)
    (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ
    (fun r => higherBandTargetScale d r N μ) hℓ (fun r hr =>
      hℓ.trans (Finset.mem_filter.mp hr).2.2.le)
  have hP := finePairAliasGeometryEnvelope_measurable (d := d) (n := n) (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η
  have hF := fineFieldGeometryEnvelope_measurable (d := d) (n := n) (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η
  unfold completeSourceHigherGeometryEnvelope
  split_ifs <;> fun_prop

 theorem completeSourceHigherGeometryEnvelope_integrable {d n D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hn : 2 ≤ n) (aD bD c0 ℓ N μ : ℝ) (M R q : ℕ) (C a ρ η : ℝ)
    (hℓ : 1 ≤ ℓ) (hN : ℓ ≤ N) :
    Integrable (completeSourceHigherGeometryEnvelope (d := d) (n := n) (D := D)
      aD bD c0 ℓ N μ M R q C a ρ η) (fullSpatialPatchDesign d n) := by
  have hA := (cardinalGeometryEnvelope_integrable_and_le (F := D) hd hn q (bD-(M : ℝ)⁻¹) C a ρ η
    (T := max 1 (higherBandTargetScale d n N μ)) (le_max_left _ _)).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (n := n) (F := D) hd
    (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ
    (fun r => higherBandTargetScale d r N μ) hℓ (fun r hr => by
      have h := (Finset.mem_filter.mp hr).2
      exact ⟨by omega, h.2.le⟩)
  have hP := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) hN M q C a ρ η).1
  have hF := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) M q C a ρ η).1
  unfold completeSourceHigherGeometryEnvelope
  split_ifs
  · exact (((hA.add hB).add hP).add hF).const_mul 4
  · exact by simpa only [Pi.add_apply, add_zero] using (hA.add hF).const_mul 4

 theorem completeSourceHigherGeometryEnvelope_integral_le {d n D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hn : 2 ≤ n) (aD bD c0 ℓ N μ : ℝ) (M R q : ℕ) (C a ρ η : ℝ)
    (hℓ : 1 ≤ ℓ) (hN : ℓ ≤ N) :
    (∫ U, completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η U
      ∂fullSpatialPatchDesign d n) ≤
      4*((3 : ℝ)^n*cardinalRawSpatialEnergyBudget d n q (bD-(M : ℝ)⁻¹) C a ρ η
          (max 1 (higherBandTargetScale d n N μ)) +
        (if M<n then ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
          (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ
          (fun r => higherBandTargetScale d r N μ) U ∂fullSpatialPatchDesign d n else 0) +
        (if M<n then (3 : ℝ)^n*finePairAliasActionSpatialBudget d n M q
          (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) C a ρ η ℓ else 0) +
        (3 : ℝ)^n*finePairEvenActionSpatialBudget d n M q
          (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) C a ρ η ℓ) := by
  have hA := cardinalGeometryEnvelope_integrable_and_le (F := D) hd hn q (bD-(M : ℝ)⁻¹) C a ρ η
    (T := max 1 (higherBandTargetScale d n N μ)) (le_max_left _ _)
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (n := n) (F := D) hd
    (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ
    (fun r => higherBandTargetScale d r N μ) hℓ (fun r hr => by
      have h := (Finset.mem_filter.mp hr).2
      exact ⟨by omega, h.2.le⟩)
  have hP := finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) hN M q C a ρ η
  have hF := fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) M q C a ρ η
  unfold completeSourceHigherGeometryEnvelope
  by_cases hMn : M<n
  · simp only [if_pos hMn]
    rw [integral_const_mul]
    have e1 := integral_add ((hA.1.add hB).add hP.1) hF.1
    have e2 := integral_add (hA.1.add hB) hP.1
    have e3 := integral_add hA.1 hB
    simp only [Pi.add_apply] at e1 e2 e3
    rw [e1, e2, e3]
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA.2 (le_refl _)) hP.2) hF.2) (by norm_num)
  · simp only [if_neg hMn, add_zero]
    rw [integral_const_mul, integral_add hA.1 hF.1]
    exact mul_le_mul_of_nonneg_left (add_le_add hA.2 hF.2) (by norm_num)

end NearlyMinimax
