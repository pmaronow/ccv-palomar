module

public import NearlyMinimax.HighSourceNuisanceGeometry
public import NearlyMinimax.PaperLowerRegimeGeometryEnergy
public import NearlyMinimax.PaperLowerRegimeAliasNorm
public import NearlyMinimax.HighGeometryEnvelopeMonotone


@[expose] public section

/-! The literal supremum-before-integration local norm has the full raw
factorial energy estimate on every tuple in the paper's Reg(K). The fixed
threshold precedes all resolutions, scales, grids and activity budgets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceRowData highRowTotalMass

theorem paperLowerRegime_uniform_local_norm_energy {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr Cs : ℝ) (hK : 1 ≤ K) (hCfr : 1 ≤ Cfr) (hCs : 0 ≤ Cs) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ k : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
      let ell := N*Real.exp (-c0*D)
      let q := lowerSaddleResponseOrder C.smoothness d
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      ∀ Bl : ℝ, highRowTotalMass R.rowMass ≤ Bl →
      (∀ r, Integrable (compactNuisanceEnergy
        (localNuisanceSet (HighFrameIndex d D) r (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v)
        (completeSourcePatchNumerator (D := D) (M := M) (q := q) (n := r)
          C Cfr (spatialInterpolationLambda d) ell N mu Q eta))
        (fullSpatialPatchDesign d r)) ∧
      ∀ J : ℕ,
        (∑ r ∈ Finset.range (J+1), poissonCountWeight (Cs*mu) r *
          completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r)
            C Cfr (spatialInterpolationLambda d) ell N mu Q eta) ≤
        paperRegimeCompleteEnergyBound C Q K Cfr Cs Bl M D N mu eta := by
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let q := lowerSaddleResponseOrder C.smoothness d
  let lam := spatialInterpolationLambda d
  let Rt := paperRegimeFineTargetBound d K c0
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hc0 : 0 < c0 := by dsimp only [c0]; linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  have hq : 2 ≤ q := le_max_left _ _
  obtain ⟨Me,hMe⟩ := paperLowerRegime_uniform_complete_geometry_energy hd C Q K Cfr Cs hK hCs
  obtain ⟨Mh,hMh⟩ := paperLowerRegime_uniform_hierarchy (NeZero.pos d) C Q K c0 1 1
    hK hc0.le (by norm_num) (by norm_num)
  have hevent : ∀ᶠ M : ℕ in atTop, Me ≤ M ∧ Mh ≤ M ∧ 2 ≤ M ∧
      highCenterResolutionThreshold C ≤ (M : ℝ) ∧
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 := by
    filter_upwards [eventually_ge_atTop Me,eventually_ge_atTop Mh,eventually_ge_atTop (2 : ℕ),
      eventually_ge_atTop (Nat.ceil (highCenterResolutionThreshold C)),
      shrunkDensityExponent_eventually_le_plus_one C.densityLower_pos hab] with M he hh hm hr ht
    exact ⟨he,hh,hm,(Nat.le_ceil _).trans (by exact_mod_cast hr),ht⟩
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hevent
  refine ⟨M0,?_⟩
  intro M D hm N mu eta Reg k hk0 horder hk
  letI := hk0
  letI := horder
  obtain ⟨hme,hmh,hm2,hres,htau⟩ := hM0 M hm
  have H := hMh M D hmh N mu eta Reg
  let ell := N*Real.exp (-c0*D)
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have hD : 3 ≤ D := by
    have hmR : (2 : ℝ) ≤ M := by exact_mod_cast hm2
    have hslope : 2 ≤ paperLowerRegimeDegreeSlope d := by
      unfold paperLowerRegimeDegreeSlope
      linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have hDr : (3 : ℝ) ≤ D := by nlinarith only [Reg.degree_lower,hmR,hslope]
    exact_mod_cast hDr
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one Reg.scale
  have hell : 0 < ell := by positivity
  have hellN : ell < N := by
    have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have he : Real.exp (-c0*D) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    exact (mul_lt_mul_of_pos_left he hN).trans_eq (mul_one N)
  have GS := completeSourceRows_guards C k D M q hD (by omega) hres Cfr lam ell N mu hCfr hell hellN
  have hnu (i : Fin (D-2)) : 0 < higherBandTargetScale d (i.val+3) N mu := by
    unfold higherBandTargetScale
    exact mul_pos hN (Real.rpow_pos_of_pos (mul_pos Reg.occupancy_positive Reg.H_positive) _)
  have hFine (i : Fin (D-2)) (hi : ell < higherBandTargetScale d (i.val+3) N mu) : i.val+3 ≤ M :=
    (H.target_count (i.val+3) hi).trans H.target_resolution
  have hI (r : ℕ) (hr : r ∈ ordinaryFineAliasTargetSet d D ell N mu) : 1 ≤ r ∧ r ≤ Rt := by
    have hh := (Finset.mem_filter.mp hr).2
    exact ⟨by omega,H.target_count r hh.2⟩
  dsimp only
  intro Bl hBl
  have hEnergy := hMe M D hme N mu eta Reg Bl
  have hNorm (r : ℕ) := completeSourcePatchEnergy_all_integrable_and_bound (n := r)
    C hD hq hres Cfr lam ell N mu hCfr hell hellN Q eta hk Reg.amplitude_positive.le Reg.amplitude_half
    (0 : HighWindowLabels d k) hd c0 Rt H.cutoff.le rfl htau hnu hFine hI
  refine ⟨fun r => (hNorm r).1,?_⟩
  have hNormLe (r : ℕ) : completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r)
      C Cfr lam ell N mu Q eta ≤
      ∫ U, paperRegimeCompleteGeometryEnvelope C Q K Cfr Bl M D N mu eta r U
        ∂fullSpatialPatchDesign d r := by
    rw [completeSourceLocalNormSq_eq_patchNorm]
    apply (hNorm r).2.trans
    apply integral_mono
      (completeSourceGeometryEnvelope_integrable hd D M Rt q C.densityLower C.densityUpper c0 ell N mu Cfr
        Q.a Q.ρ eta _ _ H.cutoff.le hellN.le r)
      (hEnergy.1 r)
    intro U
    exact completeSourceGeometryEnvelope_mono_total D M Rt q C.densityLower C.densityUpper c0 ell N mu Cfr
      Q.a Q.ρ eta (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)
      GS.total_positive.le hBl r U
  intro J
  apply le_trans (Finset.sum_le_sum (fun r hr => ?_)) (hEnergy.2 J)
  exact mul_le_mul_of_nonneg_left (hNormLe r) (poissonCountWeight_nonneg (mul_nonneg hCs Reg.occupancy_positive.le) r)

end NearlyMinimax
