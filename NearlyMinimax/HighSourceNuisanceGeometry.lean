module

public import NearlyMinimax.HighSourceNuisanceNorm
public import NearlyMinimax.HighSourceAffineTail
public import NearlyMinimax.HighCompleteGeometry


@[expose] public section

/-! All-count literal compact-nuisance energy domination for the complete
signed source. The patch supremum is genuine, including pair and exterior
counts, and its integrability follows from actual spatial geometry. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
section
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 2 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
  (Q : LowSmoothnessTernaryConstants C) (η : ℝ) (hk : 4 ≤ k)
  (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2)
local notation "K" => localNuisanceSet (HighFrameIndex d D) n
  (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v
local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
include hD hq hM hCfr hℓ hℓN hk hη hηρ

theorem completeSourcePatchNumerator_all_square_le_geometry
    (j : HighWindowLabels d k) (c0 : ℝ) (Rord : ℕ) (hL : 1 ≤ ℓ)
    (hlam : lam = spatialInterpolationLambda d)
    (htau : shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0)
    (hnu : ∀ i : Fin (D-2), 0 < higherBandTargetScale d (i.val+3) N μ)
    (hFine : ∀ i : Fin (D-2), ℓ < higherBandTargetScale d (i.val+3) N μ → i.val+3 ≤ M)
    (hI : ∀ r ∈ ordinaryFineAliasTargetSet d D ℓ N μ, 1 ≤ r ∧ r ≤ Rord)
    (z : LocalNuisance (HighFrameIndex d D) n) (hz : z ∈ K) (U : Fin n → Covariate d) :
    (∑ y, (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z U y)^2) ≤
      completeSourceGeometryEnvelope D M Rord q C.densityLower C.densityUpper c0 ℓ N μ Cfr Q.a Q.ρ η
        (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)
        (highRowTotalMass (R).rowMass) n U := by
  by_cases hU : U ∈ sourceSpatialPatchSet d n
  · obtain ⟨hp,hc,hg,hV⟩ := localNuisanceSet_guards _ n _ _ _ _ _ z hz
    have hh := high_source_interval_numeric C (M : ℝ) hM
    have hw : ∀ i, |highWindowTensor d (U i)| ≤ 1 := by
      intro i
      rw [abs_of_nonneg (highWindowTensor_nonneg d (U i))]
      exact highWindowTensor_le_one d (U i)
    have hU2 : ∀ i l, |U i l| ≤ 2 := fun i l => (hU i l).trans (by norm_num)
    have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards C (M : ℝ) hM).1
    rcases n with _|_|_|n
    · simp only [completeSourcePatchNumerator,if_pos hU,completeSourceGeometryEnvelope]
      have hz0 (y : Fin 0 → Fin 3) := completeSourceRawNumerator_count_zero _ _ lam ℓ N μ
        hh.1 hh.2 D M q (by omega) Cfr Q.a z.2.2.2 η U z.1 z.2.2.1
        (fun i => highWindowTensor d (U i)) z.2.1 y
      simp only [hz0,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero,le_refl]
    · simp only [completeSourcePatchNumerator,if_pos hU,completeSourceGeometryEnvelope]
      have hz1 (y : Fin 1 → Fin 3) := completeSourceRawNumerator_count_one _ _ lam ℓ N μ
        hh.1 hh.2 D M q (by omega) (by omega) Cfr Q.a z.2.2.2 η (by linarith)
        U hU2 z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) hp z.2.1 y
      simp only [hz1,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero,le_refl]
    · simp only [completeSourcePatchNumerator,if_pos hU,completeSourceGeometryEnvelope]
      have he (y : Fin 2 → Fin 3) :
          completeSourceRawNumerator (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) lam ℓ N μ
            D M q Cfr Q.a z.2.2.2 η U z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) z.2.1 y =
          finePairCountTwoRawNumerator (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) ℓ N
            D M q Cfr Q.a z.2.2.2 η U z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) z.2.1 y := by
        unfold completeSourceRawNumerator finePairCountTwoRawNumerator
        rw [completeSourceSignedFirstAction_eq_family,
          singletonFirstAction_zero_other_count _ _ hh.1 hh.2 D q (by omega) (by omega) (by omega)
            Cfr z.1 hp z.2.1,
          higherBandFamilyFirstAction_zero_small_count _ _ lam ℓ N μ hh.1 hh.2 D M q (by omega)
            (by omega) (by omega) Cfr U hU2 z.1 hp z.2.1]
        simp only [add_zero]
        have hprod : (∏ i : Fin 2, z.1 i) = z.1 0*z.1 1 := by
          exact Fin.prod_univ_two z.1
        rw [hprod]
      simp_rw [he]
      have hf (i) : |coefficientRegression η z.2.2.1 (fun i => highWindowTensor d (U i))
          (fun i => highFrameFeature (U i)) z.2.1 i| ≤ Q.ρ :=
        highFrameCoefficientRegression_abs_le Cfr η Q.ρ hCfr hη hηρ U hU2 z.2.2.1
          (fun i => highWindowTensor d (U i)) hg hw z.2.1 hc i
      simpa only [one_div] using finePairCountTwoRawNumerator_sum_square_le_geometry hD _ _ ℓ N
        hh.1 hh.2 hℓ.le hℓN.le D M q (by omega) hM2 hq Cfr Q.a z.2.2.2 η Q.ρ (by linarith)
        Q.a_pos Q.ρ_pos.le U (fun i => hU i) z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) hp hw z.2.1 hf
    · by_cases hnD : n+3 ≤ D
      · change _ ≤ if n+3≤D then _ else _
        rw [if_pos hnD]
        simp only [completeSourcePatchNumerator,if_pos hU]
        rw [hlam]
        have hpD := hp
        simp only [one_div] at hpD
        simpa only [one_div] using completeSourceRawNumerator_higher_square_le_geometry C.densityLower C.densityUpper
          c0 ℓ N μ C.densityLower_pos hL D M Rord q (by simpa only [one_div] using hh.2)
          htau (by omega) hnD (by omega) hnu hFine hI Cfr Q.a z.2.2.2 η Q.ρ hCfr Q.a_pos hη Q.ρ_pos.le hηρ
          U hU2 z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) hpD hg hw z.2.1 hc
          (fun f hf b => Q.c_pos.le.trans ((Q.legal f _ hf hV).2.2.1 b))
      · change _ ≤ if n+3≤D then _ else _
        rw [if_neg hnD]
        let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
        have G := completeSourceRows_guards C k D M q hD (by omega) hM Cfr lam ℓ N μ hCfr hℓ hℓN
        have hb (W : Fin (n+3) → Covariate d) (y : Fin (n+3) → Fin 3) :
            |completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z W y| ≤
              Chi^(n+3)*η^2*(highRowTotalMass (R).rowMass+1) := by
          by_cases hW : W ∈ sourceSpatialPatchSet d (n+3)
          · rw [completeSourcePatchNumerator_eq_marked_inverse C hD (by omega) hM Cfr lam ℓ N μ
              hCfr hℓ hℓN Q η hk hη hηρ j z hz W hW y]
            exact completeSourceNuisanceNumerator_all_count_bound C hD (by omega) hM Cfr lam ℓ N μ
              hCfr hℓ hℓN (by omega) Q η (by omega) hη hηρ j z hz _ y
          · simp only [completeSourcePatchNumerator,if_neg hW,abs_zero]
            have hChi : 0 < Chi := highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1
            positivity [G.total_positive.le]
        have ht := crude_raw_square_energy_pointwise Chi η (highRowTotalMass (R).rowMass)
          (highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1).le G.total_positive.le
          (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z) hb U
        have he : (∑ y : Fin (n+3) → Fin 3,
            completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z U y^2) =
            selectedRawSquareEnergy (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z) U := by
          unfold selectedRawSquareEnergy
          apply Finset.sum_congr (by ext y; simp)
          intro y _
          rfl
        exact he.trans_le ht
  · simp only [completeSourcePatchNumerator,if_neg hU,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero]
    exact completeSourceGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem completeSourcePatchEnergy_all_integrable_and_bound
    (j : HighWindowLabels d k) (hd : 5 ≤ d) (c0 : ℝ) (Rord : ℕ) (hL : 1 ≤ ℓ)
    (hlam : lam = spatialInterpolationLambda d)
    (htau : shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0)
    (hnu : ∀ i : Fin (D-2), 0 < higherBandTargetScale d (i.val+3) N μ)
    (hFine : ∀ i : Fin (D-2), ℓ < higherBandTargetScale d (i.val+3) N μ → i.val+3 ≤ M)
    (hI : ∀ r ∈ ordinaryFineAliasTargetSet d D ℓ N μ, 1 ≤ r ∧ r ≤ Rord) :
    Integrable (compactNuisanceEnergy K
      (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η))
        (fullSpatialPatchDesign d n) ∧
    (∫ U, compactNuisanceEnergy K
      (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η) U ∂fullSpatialPatchDesign d n) ≤
      ∫ U, completeSourceGeometryEnvelope D M Rord q C.densityLower C.densityUpper c0 ℓ N μ Cfr Q.a Q.ρ η
        (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)
        (highRowTotalMass (R).rowMass) n U ∂fullSpatialPatchDesign d n := by
  apply compactNuisanceEnergy_integrable_and_bound (fullSpatialPatchDesign d n) K
    (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (localNuisanceSet_nonempty _ _ (high_source_interval_numeric C (M : ℝ) hM).2.le
      (by linarith) Q.ρ_pos.le)
    (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η)
    ?_ ?_
    (completeSourceGeometryEnvelope (d := d) D M Rord q C.densityLower C.densityUpper c0 ℓ N μ Cfr Q.a Q.ρ η
      (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) (highRowTotalMass (R).rowMass) n)
    (completeSourceGeometryEnvelope_integrable hd D M Rord q C.densityLower C.densityUpper c0 ℓ N μ Cfr Q.a Q.ρ η
      _ _ hL hℓN.le n) ?_
  · intro z hz y
    exact completeSourcePatchNumerator_measurable C hD (by omega) hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j z hz y
  · intro U y
    exact completeSourcePatchNumerator_continuousOn C hD (by omega) hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j U y
  · exact completeSourcePatchNumerator_all_square_le_geometry C hD hq hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j c0 Rord hL hlam htau hnu hFine hI
end
end NearlyMinimax
