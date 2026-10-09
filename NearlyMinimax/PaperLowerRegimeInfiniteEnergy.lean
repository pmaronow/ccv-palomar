module

public import NearlyMinimax.PaperLowerRegimeNormEnergy


@[expose] public section

/-! The literal infinite count series of supremum-before-integration
complete source norms. Summability and its bound follow from the verified
true nonnegative finite count energies on every tuple in Reg(K). -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

 def paperRegimeLocalEnergy {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr Cs : ℝ) (M D : ℕ) (N mu eta : ℝ) : ℝ :=
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let ell := N*Real.exp (-c0*D)
  let q := lowerSaddleResponseOrder C.smoothness d
  ∑' r : ℕ, poissonCountWeight (Cs*mu) r*
    completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r)
      C Cfr (spatialInterpolationLambda d) ell N mu Q eta

 theorem completeSourceLocalNormSq_nonneg {d k D M q n : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ)) (Cfr lam ell N mu : ℝ)
    (hCfr : 1 ≤ Cfr) (hell : 0 < ell) (hellN : ell < N)
    (Q : LowSmoothnessTernaryConstants C) (eta : ℝ) (hk : 4 ≤ k)
    (heta : 0 ≤ eta) (hetaRho : eta ≤ Q.ρ/2) :
    0 ≤ completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := n) C Cfr lam ell N mu Q eta := by
  rw [completeSourceLocalNormSq_eq_patchNorm]
  apply integral_nonneg
  intro U
  exact compactNuisanceEnergy_nonneg _ (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (localNuisanceSet_nonempty _ _ (high_source_interval_numeric C (M : ℝ) hM).2.le (by linarith) Q.ρ_pos.le)
    _ (fun W y => completeSourcePatchNumerator_continuousOn C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaRho (0 : HighWindowLabels d k) W y) U

 theorem paperLowerRegime_uniform_local_norm_infinite_energy {d : ℕ} [NeZero d]
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
      Summable (fun r : ℕ => poissonCountWeight (Cs*mu) r*
        completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r)
          C Cfr (spatialInterpolationLambda d) ell N mu Q eta) ∧
      paperRegimeLocalEnergy C Q Cfr Cs M D N mu eta ≤
        paperRegimeCompleteEnergyBound C Q K Cfr Cs Bl M D N mu eta := by
  obtain ⟨Mn,hMn⟩ := paperLowerRegime_uniform_local_norm_energy hd C Q K Cfr Cs hK hCfr hCs
  obtain ⟨Ms,hMs⟩ := paperLowerRegime_uniform_source_guards C Q K Cfr (spatialInterpolationLambda d)
    hK hCfr (lowerSaddleResponseOrder C.smoothness d) (by unfold lowerSaddleResponseOrder; omega)
  let M0 := max Mn Ms
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R k hk0 horder hk
  letI := hk0
  letI := horder
  dsimp only
  intro Bl hBl
  let q := lowerSaddleResponseOrder C.smoothness d
  let ell := N*Real.exp (-(densityIntervalExponent C.densityLower C.densityUpper+1)*D)
  let lam := spatialInterpolationLambda d
  have hn := hMn M D ((le_max_left _ _).trans hm) N mu eta R k hk0 horder hk Bl hBl
  have GS := (hMs M D ((le_max_right _ _).trans hm) N mu eta R k).1
  have hq : 1 ≤ q := by dsimp only [q,lowerSaddleResponseOrder]; omega
  have hell : 0 < ell := by dsimp only [ell]; positivity [lt_of_lt_of_le zero_lt_one R.scale]
  have hc0 : 0 < densityIntervalExponent C.densityLower C.densityUpper+1 := by
    linarith [densityIntervalExponent_pos C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)]
  have hellN : ell < N := by
    have hD : (0 : ℝ) < D := by
      have hMpos : (0 : ℝ) < M := by linarith [(highCenterResolution_guards C (M : ℝ) GS.resolution).1]
      exact (mul_pos (paperLowerRegimeDegreeSlope_positive d) hMpos).trans_le R.degree_lower
    have he : Real.exp (-(densityIntervalExponent C.densityLower C.densityUpper+1)*D) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith)
    exact (mul_lt_mul_of_pos_left he (lt_of_lt_of_le zero_lt_one R.scale)).trans_eq (mul_one N)
  have hD : 3 ≤ D := by
    have hM2 : (2 : ℝ) ≤ M := (highCenterResolution_guards C (M : ℝ) GS.resolution).1
    have hslope : 2 ≤ paperLowerRegimeDegreeSlope d := by
      unfold paperLowerRegimeDegreeSlope
      linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have hh : (3 : ℝ) ≤ D := by nlinarith only [hM2,hslope,R.degree_lower]
    exact_mod_cast hh
  let f := fun r : ℕ => poissonCountWeight (Cs*mu) r*
    completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r) C Cfr lam ell N mu Q eta
  have hf (r : ℕ) : 0 ≤ f r := mul_nonneg (poissonCountWeight_nonneg (mul_nonneg hCs R.occupancy_positive.le) r)
    (completeSourceLocalNormSq_nonneg C hD hq GS.resolution Cfr lam ell N mu hCfr hell hellN Q eta
      hk R.amplitude_positive.le R.amplitude_half)
  have hprefix (J : ℕ) : (∑ r ∈ Finset.range J, f r) ≤ paperRegimeCompleteEnergyBound C Q K Cfr Cs Bl M D N mu eta := by
    apply le_trans _ (hn.2 J)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ J)) (fun r _ _ => hf r)
  refine ⟨summable_of_sum_range_le hf hprefix,?_⟩
  exact Real.tsum_le_of_sum_range_le hf hprefix

end NearlyMinimax
