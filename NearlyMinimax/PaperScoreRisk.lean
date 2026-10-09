module

public import NearlyMinimax.HighCompleteIntrinsicCostExact
public import NearlyMinimax.ExactSourceCompactEnergy
public import NearlyMinimax.SourceIncomingNuisance
public import NearlyMinimax.PaperScoreRiskNumerics
public import NearlyMinimax.HighMassTailScale
public import NearlyMinimax.HighExactSourceEnergy


@[expose] public section

/-! The literal local-cost proposition, with the paper's intrinsic frame,
amplitude cutoff, exact chart constant, actual compact-nuisance infinite
energy and exceptional-mass tail. All constants are fixed before U. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The manuscript's fixed score-series coefficient C_sharp. -/
def paperSourceScoreConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) : ℝ := 1/(C.densityLower^2*Q.c)

/-- The literal score-to-risk proposition. The energy is defined by the
actual numerator and compact nuisance supremum; its finiteness and every
Fisher/path estimate are proved inside this endpoint. -/
theorem paper_score_risk {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ ctr : ℝ, 0 < ctr ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q →
      highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ lam ell N mu : ℝ, 0 < ell → ell < N →
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ Q.ρ/(2 : ℝ)^(d+1) →
      ∀ n : ℕ, mu = (n : ℝ)*(1/(k : ℝ))^d →
      let cm := 1/(2*C.densityUpper)
      8*highHistoryMassMomentConstant d C.densityLower C.densityUpper*mu ≤ cm/(M : ℝ) →
      let R := completeSourceRows C k D M q (highIntrinsicFrameConstant C) lam ell N mu
      let Bl := highRowTotalMass R.rowMass/highCenterMix C
      let E := exactSourceLiteralEnergy (D := D) (M := M) (q := q) C Q
        (highIntrinsicFrameConstant C) lam ell N mu eta (paperSourceScoreConstant C Q*mu)
      let eps := 2*Real.exp (-(cm^2)/
        (8*highHistoryMassMomentConstant d C.densityLower C.densityUpper*(M : ℝ)^2*(1/(k : ℝ))^d))
      ENNReal.ofReal (ctr*eta^4/(1+Bl^2+(k : ℝ)^d*E)-
        (C.varianceUpper-C.varianceLower)^2*eps) ≤ minimaxRisk (C.withDomain U) n := by
  obtain ⟨ctr,hctr,hcost⟩ := highCompleteSource_intrinsic_cost_risk_exact C Q
  refine ⟨ctr,hctr,?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN cf hcf hcfH
  letI := hk0
  letI := horder
  dsimp only
  intro heta n hmu heps
  let Cfr := highIntrinsicFrameConstant C
  let eta0 := Q.ρ/(2 : ℝ)^(d+1)
  let eta := cf*(k : ℝ)^(-C.smoothness)
  let cm := 1/(2*C.densityUpper)
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
  let Bl := highRowTotalMass R.rowMass/highCenterMix C
  let X := (n : ℝ)*highFixedScoreDenominator C.densityLower Q.c*(1/(k : ℝ))^d
  let E := exactSourceLiteralEnergy (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta X
  let H := exactSourceCompactEnvelope (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta
  let c := highPathConstant (3^d) Q.ρ eta0
  let I := Real.sqrt ((3^d : ℕ)*(k : ℝ)^d*E)
  let delta := localScorePathLength c Bl I
  have hCfr : 1 ≤ Cfr := highIntrinsicFrameConstant_ge_one C
  have heta0 : 0 < eta0 := div_pos Q.ρ_pos (by positivity)
  have hetaN : 0 ≤ eta := mul_nonneg hcf (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hetaHalf : eta ≤ Q.ρ/2 := sourceIntrinsicAmplitude_le_half hetaN heta
  have hx : 0 ≤ X := by dsimp only [X]; positivity [high_fixed_score_denominator_pos C.densityLower_pos Q.c_pos]
  have hE : 0 ≤ E := exactSourceLiteralEnergy_nonneg C hD hq hM Cfr lam ell N mu
    hCfr hell hellN Q eta hk hetaN hetaHalf X hx
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  have hBl : 0 ≤ Bl := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hI : 0 ≤ I := Real.sqrt_nonneg _
  have hVbudget := highPath_variance_budget (3^d) Q.ρ_pos heta0 hBl hI hetaN heta
  have hV (t : ℝ) (ht : t ∈ Icc 0 delta) : Q.v-eta^2*t ∈ Icc (Q.v-Q.ρ) Q.v := by
    constructor
    · have hh := (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hVbudget
      linarith
    · linarith [mul_nonneg (sq_nonneg eta) ht.1]
  have hH (r : ℕ) : Integrable (H r)
      (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))) :=
    exactSourceCompactEnvelope_integrable C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk hetaN hetaHalf r
  have hH0 (r : ℕ) (u : Fin r → Covariate d) : 0 ≤ H r u :=
    exactSourceCompactEnvelope_nonneg C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk hetaN hetaHalf r u
  have hdom (t : ℝ) (ht : t ∈ Icc 0 delta) (h : Ω) (j : HighWindowLabels d k)
      (r : ℕ) (x : Fin r → Covariate d) (hpatch : ∀ i, x i ∈ highTorusPatch d k j) :
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v-eta^2*t) eta h j) x ≤
        H r (highPatchProductChart d k j x) :=
    completeSourceIncomingRawEnergy_le C Q hk hD hq hM Cfr lam ell N mu eta (Q.v-eta^2*t)
      le_rfl hell hellN hetaN heta (hV t ht) h j x hpatch
  have hseries : highSourceSpatialSeriesExact d k n C.densityLower Q.c (fun _ => H) ≤
      (3^d : ℕ)*(k : ℝ)^d*E :=
    highSourceSpatialSeriesExact_literal_energy_le C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk hetaN hetaHalf n
  have hcm : 0 ≤ cm := by dsimp only [cm]; positivity [(zero_lt_one.trans C.one_lt_densityUpper)]
  have hcmU : cm ≤ 1/C.densityUpper := by
    dsimp only [cm]
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (zero_lt_one.trans C.one_lt_densityUpper)
    linarith [(zero_lt_one.trans C.one_lt_densityUpper)]
  have hguard : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n : ℝ) ≤ cm/(M : ℝ) := by
    rw [highHistoryMassParameter_eq_hpower d k _ _ (by omega)]
    apply le_trans _ heps
    rw [hmu]
    simp only [one_div]
    ring_nf
    exact le_rfl
  have hh := hcost U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
    cf hcf hcfH heta cm hcm hcmU n E hE hguard (fun _ _ _ => H)
    (fun _ _ _ _ r => hH r) (fun _ _ _ _ r u => hH0 r u)
    hdom (fun _ _ _ => hseries)
  have hX : X = paperSourceScoreConstant C Q*mu := by
    dsimp only [X,paperSourceScoreConstant,highFixedScoreDenominator]
    rw [hmu]
    ring
  have htail : 2*Real.exp (-(cm/(M : ℝ))^2/
      (8*highHistoryMassParameter d k C.densityLower C.densityUpper)) =
      2*Real.exp (-(cm^2)/(8*highHistoryMassMomentConstant d C.densityLower C.densityUpper*
        (M : ℝ)^2*(1/(k : ℝ))^d)) := by
    rw [highHistoryMassParameter_eq_hpower d k _ _ (by omega)]
    congr 2
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  have heps0 : 0 ≤ 2*Real.exp (-(cm/(M : ℝ))^2/
      (8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by positivity
  have hweak := (ENNReal.ofReal_le_ofReal (paper_score_original_width_loss_le C
    (ctr*eta^4/(1+Bl^2+(k : ℝ)^d*E)) _ heps0)).trans hh
  simpa only [E,Cfr,eta,cm,Bl,R,hX,htail] using hweak

end NearlyMinimax
