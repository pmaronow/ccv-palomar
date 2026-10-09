module

public import NearlyMinimax.HighExactNormSeries
public import NearlyMinimax.ExactSourceCompactEnergy


@[expose] public section

/-! The actual exact-chart finite source Fisher series is bounded by the
manuscript's literal infinite local energy with unchanged C_sharp. All
summability and numerator-norm properties are proved from the construction. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem highSourceSpatialSeriesExact_literal_energy_le {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ell N mu : ℝ) (hCfr : 1 ≤ Cfr) (hell : 0 < ell) (hellN : ell < N)
    (Q : LowSmoothnessTernaryConstants C) (eta : ℝ) (hk : 4 ≤ k)
    (heta : 0 ≤ eta) (hetaQ : eta ≤ Q.ρ/2) (n : ℕ) :
    highSourceSpatialSeriesExact d k n C.densityLower Q.c
      (fun _ => exactSourceCompactEnvelope (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta) ≤
      (3^d : ℕ)*(k : ℝ)^d *
        exactSourceLiteralEnergy (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta
          ((n : ℝ)*highFixedScoreDenominator C.densityLower Q.c*(1/(k : ℝ))^d) := by
  let H := exactSourceCompactEnvelope (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta
  let x := (n : ℝ)*highFixedScoreDenominator C.densityLower Q.c*(1/(k : ℝ))^d
  have hx : 0 ≤ x := by positivity [high_fixed_score_denominator_pos C.densityLower_pos Q.c_pos]
  have hs := exactSourceLiteralEnergy_summable C hD hq hM Cfr lam ell N mu hCfr hell hellN
    Q eta hk heta hetaQ x hx
  have hHsum : Summable (fun r : ℕ => poissonCountWeight x r *
      ∫ U, H r U ∂fullSpatialPatchDesign d r) := by
    dsimp only [H]
    simp_rw [exactSourceCompactEnvelope_integral_eq C hD hq hM Cfr lam ell N mu hCfr hell hellN
      Q eta hk heta hetaQ]
    exact hs
  have ht := highSourceSpatialSeriesExact_const_le_tsum n C.densityLower Q.c C.densityLower_pos Q.c_pos H
    (exactSourceCompactEnvelope_nonneg C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ) hHsum
  apply ht.trans_eq
  apply congrArg (fun a : ℝ => (3^d : ℕ)*(k : ℝ)^d*a)
  dsimp only [exactSourceLiteralEnergy]
  apply tsum_congr
  intro r
  rw [exactSourceCompactEnvelope_integral_eq C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r]

end NearlyMinimax
