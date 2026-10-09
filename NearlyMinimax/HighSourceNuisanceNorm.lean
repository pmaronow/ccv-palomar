module

public import NearlyMinimax.HighUnionNuisanceRegularity
public import NearlyMinimax.HighUnionNuisanceJoint
public import NearlyMinimax.HighChartInverse
public import NearlyMinimax.HighSourceHigherGeometry


@[expose] public section

/-! The actual source numerator in literal spatial patch coordinates and
the manuscript's supremum-before-integration norm. No nuisance supremum
measurability or source-numerator continuity is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

def sourceSpatialPatchSet (d n : ℕ) : Set (Fin n → Covariate d) :=
  {U | ∀ i l, |U i l| ≤ 1}

theorem sourceSpatialPatchSet_measurable (d n : ℕ) : MeasurableSet (sourceSpatialPatchSet d n) := by
  unfold sourceSpatialPatchSet
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro l
  exact measurableSet_le (((measurable_pi_apply l).comp (measurable_pi_apply i)).abs) measurable_const

section
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
  (Q : LowSmoothnessTernaryConstants C) (η : ℝ) (hk : 4 ≤ k)
  (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2)

local notation "K" => localNuisanceSet (HighFrameIndex d D) n
  (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v
local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ

def completeSourcePatchNumerator (z : LocalNuisance (HighFrameIndex d D) n)
    (U : Fin n → Covariate d) (y : Fin n → Fin 3) : ℝ :=
  if U ∈ sourceSpatialPatchSet d n then
    completeSourceRawNumerator (C.densityLower+1/(M : ℝ))
      (C.densityUpper-1/(M : ℝ)) lam ℓ N μ D M q Cfr Q.a z.2.2.2 η
      U z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) z.2.1 y
  else 0

def completeSourceLocalNormSq : ℝ :=
  ∫ U, compactNuisanceEnergy K (fun z U y =>
    completeSourceRawNumerator (C.densityLower+1/(M : ℝ))
      (C.densityUpper-1/(M : ℝ)) lam ℓ N μ D M q Cfr Q.a z.2.2.2 η
      U z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) z.2.1 y) U
    ∂fullSpatialPatchDesign d n

theorem completeSourceLocalNormSq_eq_patchNorm :
    completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := n) C Cfr lam ℓ N μ Q η =
      ∫ U, compactNuisanceEnergy K
        (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η) U
        ∂fullSpatialPatchDesign d n := by
  apply integral_congr_ae
  filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
  simp only [compactNuisanceEnergy,completeSourcePatchNumerator,
    if_pos (show U ∈ sourceSpatialPatchSet d n from hU)]

include hD hq hM hCfr hℓ hℓN hk hη hηρ

theorem completeSourcePatchNumerator_eq_marked_inverse
    (j : HighWindowLabels d k) (z : LocalNuisance (HighFrameIndex d D) n) (hz : z ∈ K)
    (U : Fin n → Covariate d) (hU : U ∈ sourceSpatialPatchSet d n) (y : Fin n → Fin 3) :
    completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z U y =
      highUnionNuisanceNumerator C R Q η j z (highChartConfigurationInverse d k j U) y := by
  have he := completeSourceNuisanceNumerator_eq_signed C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN Q η (by omega) hη hηρ j z hz
    (highChartConfigurationInverse d k j U) y
  rw [highChartConfigurationInverse_localCoordinates d k hk j U hU] at he
  have hw : (fun u => highPeriodicTensor d k j (highChartConfigurationInverse d k j U u)) =
      (fun u => highWindowTensor d (U u)) := by
    funext u
    exact highPeriodicTensor_inverse d k hk j (U u) (hU u)
  rw [hw] at he
  simpa only [completeSourcePatchNumerator, if_pos hU] using he.symm

theorem completeSourcePatchNumerator_measurable
    (j : HighWindowLabels d k) (z : LocalNuisance (HighFrameIndex d D) n) (hz : z ∈ K)
    (y : Fin n → Fin 3) :
    Measurable (fun U => completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z U y) := by
  classical
  let G : HighUnionSourceGuards C (M : ℝ) Cfr R := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  have hm : Measurable (fun U : Fin n → Covariate d =>
      highUnionNuisanceNumerator C R Q η j z (highChartConfigurationInverse d k j U) y) :=
    (highUnionNuisanceNumerator_measurable C R Q η j G z y).comp
      (highChartConfigurationInverse_measurable (n := n) d k j)
  have hi := hm.indicator (sourceSpatialPatchSet_measurable d n)
  convert hi using 1
  funext U
  by_cases hU : U ∈ sourceSpatialPatchSet d n
  · simp only [Set.indicator_of_mem hU]
    exact completeSourcePatchNumerator_eq_marked_inverse C hD hq hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j z hz U hU y
  · simp [completeSourcePatchNumerator, Set.indicator, hU]

theorem completeSourcePatchNumerator_continuousOn
    (j : HighWindowLabels d k) (U : Fin n → Covariate d) (y : Fin n → Fin 3) :
    ContinuousOn (fun z => completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η z U y) K := by
  by_cases hU : U ∈ sourceSpatialPatchSet d n
  · let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
    apply (highUnionNuisanceNumerator_continuousOn C R Q η j G (by omega)
      hη hηρ (highChartConfigurationInverse d k j U) y).congr
    intro z hz
    exact completeSourcePatchNumerator_eq_marked_inverse C hD hq hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j z hz U hU y
  · simpa only [completeSourcePatchNumerator, if_neg hU] using
      (continuousOn_const : ContinuousOn (fun _ : LocalNuisance (HighFrameIndex d D) n => (0 : ℝ)) K)

theorem completeSourcePatchEnergy_measurable (j : HighWindowLabels d k) :
    Measurable (compactNuisanceEnergy K (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η)) := by
  apply compactNuisanceEnergy_measurable
  · exact localNuisanceSet_isCompact _ _ _ _ _ _ _
  · exact localNuisanceSet_nonempty _ _
      (high_source_interval_numeric C (M : ℝ) hM).2.le (by linarith) Q.ρ_pos.le
  · intro z hz y
    exact completeSourcePatchNumerator_measurable C hD hq hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j z hz y
  · intro U y
    exact completeSourcePatchNumerator_continuousOn C hD hq hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j U y

theorem completeSourcePatchEnergy_higher_integrable_and_bound
    (j : HighWindowLabels d k) (hd : 5 ≤ d) (hn : 3 ≤ n) (hnD : n ≤ D)
    (c0 : ℝ) (Rord : ℕ) (hL : 1 ≤ ℓ) (hlam : lam = spatialInterpolationLambda d)
    (htau : shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0)
    (hnu : ∀ i : Fin (D-2), 0 < higherBandTargetScale d (i.val+3) N μ)
    (hFine : ∀ i : Fin (D-2), ℓ < higherBandTargetScale d (i.val+3) N μ → i.val+3 ≤ M)
    (hI : ∀ r ∈ ordinaryFineAliasTargetSet d D ℓ N μ, 1 ≤ r ∧ r ≤ Rord) :
    Integrable (compactNuisanceEnergy K
      (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η))
        (fullSpatialPatchDesign d n) ∧
    (∫ U, compactNuisanceEnergy K
      (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η) U
        ∂fullSpatialPatchDesign d n) ≤
      ∫ U, completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper
        c0 ℓ N μ M Rord q Cfr Q.a Q.ρ η U ∂fullSpatialPatchDesign d n := by
  apply compactNuisanceEnergy_integrable_and_bound (fullSpatialPatchDesign d n) K
    (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (localNuisanceSet_nonempty _ _ (high_source_interval_numeric C (M : ℝ) hM).2.le
      (by linarith) Q.ρ_pos.le)
    (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η)
    ?_ ?_
    (completeSourceHigherGeometryEnvelope (d := d) (n := n) (D := D)
      C.densityLower C.densityUpper c0 ℓ N μ M Rord q Cfr Q.a Q.ρ η)
    (completeSourceHigherGeometryEnvelope_integrable hd (by omega)
      _ _ c0 ℓ N μ M Rord q Cfr Q.a Q.ρ η hL hℓN.le) ?_
  · intro z hz y
    exact completeSourcePatchNumerator_measurable C hD hq hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j z hz y
  · intro U y
    exact completeSourcePatchNumerator_continuousOn C hD hq hM Cfr lam ℓ N μ
      hCfr hℓ hℓN Q η hk hη hηρ j U y
  · intro z hz U
    by_cases hU : U ∈ sourceSpatialPatchSet d n
    · obtain ⟨hp,hc,hg,hV⟩ := localNuisanceSet_guards _ n _ _ _ _ _ z hz
      simp only [completeSourcePatchNumerator,if_pos hU]
      rw [hlam]
      have hU2 : ∀ i l, |U i l| ≤ 2 := fun i l => (hU i l).trans (by norm_num)
      have hpD : ∀ i, z.1 i ∈ Icc (C.densityLower+(M : ℝ)⁻¹)
          (C.densityUpper-(M : ℝ)⁻¹) := by simpa only [one_div] using hp
      have hw : ∀ i, |highWindowTensor d (U i)| ≤ 1 := by
        intro i
        rw [abs_of_nonneg (highWindowTensor_nonneg d (U i))]
        exact highWindowTensor_le_one d (U i)
      have hprob : ∀ f : ℝ, |f| ≤ Q.ρ → ∀ b, 0 ≤ ternaryMass Q.a f z.2.2.2 b :=
        fun f hf b => Q.c_pos.le.trans ((Q.legal f _ hf hV).2.2.1 b)
      simpa only [one_div] using (completeSourceRawNumerator_higher_square_le_geometry C.densityLower C.densityUpper
        c0 ℓ N μ C.densityLower_pos hL D M Rord q
        (by simpa only [one_div] using (high_source_interval_numeric C (M : ℝ) hM).2)
        htau hn hnD hq hnu hFine hI Cfr Q.a z.2.2.2 η Q.ρ hCfr Q.a_pos hη Q.ρ_pos.le hηρ
        U hU2 z.1 z.2.2.1 (fun i => highWindowTensor d (U i)) hpD hg hw z.2.1 hc hprob)
    · simp only [completeSourcePatchNumerator,if_neg hU,zero_pow (by norm_num : 2 ≠ 0),
        Finset.sum_const_zero]
      exact completeSourceHigherGeometryEnvelope_nonneg _ _ c0 ℓ N μ M Rord q Cfr Q.a Q.ρ η U

end
end NearlyMinimax
