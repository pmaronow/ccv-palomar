module

public import NearlyMinimax.CompleteSaddleEnergyWitness
public import NearlyMinimax.CompleteSaddleRiskReduction
public import NearlyMinimax.HighCompleteCostFlexible


@[expose] public section

/-! The original sharp lower bound. The actual complete singleton, pair,
and higher-band source supplies the raw spatial energy, legal normalized
model path and exceptional mass estimate. Every constant precedes the
extension domain and sample size. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceRowData highRowTotalMass
  highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem paper_lower_sharp {d : ℕ} (C : ModelConstants d) : LowerSharpClaim C := by
  classical
  intro hreg
  obtain ⟨hs,hd⟩ := hreg
  letI : NeZero d := NeZero.of_pos C.dimension_pos
  obtain ⟨Q⟩ := lowSmoothnessTernaryConstants_exists C
  obtain ⟨Cfr0,etaG,hCfr0,hetaG,hgeometry⟩ := completeSaddleGeometry_witness C Q hs hd
  obtain ⟨Cfr,eta0,ctr,hCfr,hmin,heta0,hctr,hcost⟩ :=
    highCompleteSource_cost_risk_uniform_above C Q Cfr0
  obtain ⟨cf,cm,hcf,hHolder,hcm,hcmU⟩ := completeSourceSaddle_numeric_constants C
  let q := lowerSaddleResponseOrder C.smoothness d
  let lam := spatialInterpolationLambda d
  let CB := completeSourceSaddleActivityConstant C q Cfr lam
  let C5 := completeSaddleDefectConstant C Q Cfr
  let C6 := completeSaddleAliasConstant C Q Cfr
  let C7 := completeSaddleFieldConstant C Q Cfr
  let ch := completeSaddleExteriorConstant C Q
  have hCB : 0 ≤ CB := (completeSourceSaddleActivityConstant_pos C q Cfr lam).le
  have hC5 : 0 ≤ C5 := (completeSaddleDefectConstant_pos C Q Cfr).le
  have hC6 : 0 ≤ C6 := (completeSaddleAliasConstant_pos C Q Cfr).le
  have hC7 : 0 ≤ C7 := (completeSaddleFieldConstant_pos C Q Cfr).le
  have hch : 0 ≤ ch := (completeSaddleExteriorConstant_pos C Q).le
  apply completeSaddle_lower_rate_of_actual_cost_budget C hs hd hcf hCB hC5 hC6 hC7 hch hctr hcm
  intro Cω
  filter_upwards [hgeometry Cfr cf hmin hcf Cω,
    tendsto_natCast_atTop_atTop.eventually
      (eventually_completeSourceSaddle_parameters C hs hd hcf heta0 hcm Cω),
    tendsto_natCast_atTop_atTop.eventually
      (completeSourceSaddleActivity_eventually_bound C hs hd q Cfr lam Cω)] with n hgeo hp hactivity
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let k := lowerSaddleGrid d m theta Cω n
  let M := completeSaddleM C n
  let D := completeSaddleD C n
  let N := completeSaddleN C Cω n
  let ell := completeSaddleEll C Cω n
  let mu := completeSaddleMu C Cω n
  let eta := cf*(k : ℝ)^(-C.smoothness)
  dsimp only at hp hgeo
  obtain ⟨hk,hD,hM,hell,hellN,heta,heps,hB⟩ := hp
  have hk' : 4 ≤ k := hk
  have hD' : 3 ≤ D := hD
  have hM' : highCenterResolutionThreshold C ≤ (M : ℝ) := hM
  letI : NeZero k := ⟨by omega⟩
  letI : LinearOrder (HighWindowLabels d k) :=
    LinearOrder.lift' (Fintype.equivFin (HighWindowLabels d k))
      (Fintype.equivFin (HighWindowLabels d k)).injective
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  obtain ⟨E,hE,hEcap,hHI,hH0,hdom,hseries⟩ := hgeo inferInstance inferInstance
  have hq : 1 ≤ q := by dsimp only [q,lowerSaddleResponseOrder]; omega
  have G := completeSourceRows_guards C k D M q hD' hq hM' Cfr lam ell N mu hCfr hell hellN
  let Bl := highRowTotalMass R.rowMass/highCenterMix C
  have hBl : 0 ≤ Bl := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hactivity' : Bl ≤ CB*lowerSaddleActivity C.smoothness d m theta Cω
      (shrunkDensityExponent C.densityLower C.densityUpper) n := hactivity
  change CompleteSaddleCostRiskBudget C cf CB C5 C6 C7 ch ctr cm Cω n
  dsimp only [CompleteSaddleCostRiskBudget]
  refine ⟨Bl,E,hB,hBl,hE,hactivity',hEcap,?_⟩
  intro U
  let I := Real.sqrt ((3^d : ℕ)*(k : ℝ)^d*E)
  let delta := localScorePathLength (highPathConstant (3^d) Q.ρ eta0) Bl I
  have heta0' : 0 ≤ eta := mul_nonneg hcf.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hvariance : eta^2*delta ≤ Q.ρ := highPath_variance_budget (3^d) Q.ρ_pos heta0 hBl
    (Real.sqrt_nonneg _) heta0' heta
  have hV (t : ℝ) (ht : t ∈ Icc 0 delta) : |(Q.v-eta^2*t)-Q.v| ≤ Q.ρ := by
    simp only [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg eta),abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hvariance
  have hetaEq : eta = completeSaddleEta C Cω cf n := completeSourceSaddle_eta_eq C Cω cf n
  have hout := hcost U k D M q inferInstance inferInstance hk' hD' hq hM' lam ell N mu hell hellN
    cf hcf.le hHolder heta cm hcm.le hcmU n E hE heps
    (fun _t _h _j r => completeSaddleGeometryEnvelope C Q Cfr cf Cω n r)
    (fun _t _ht _h _j r => hHI r)
    (fun _t _ht _h _j r u => hH0 r u)
    (fun t ht h j r x hx => by
      simpa only [← hetaEq] using hdom (Q.v-eta^2*t) (hV t ht) h j r x hx)
    (fun _t _ht _h => hseries)
  have htail : 2*Real.exp (-(cm/(M : ℝ))^2/
      (8*highHistoryMassParameter d k C.densityLower C.densityUpper)) =
      highCompleteSourceSaddleTail C Cω cm n :=
    highHistoryMass_saddle_tail_eq d m theta Cω cm C.densityLower C.densityUpper n
  simpa only [htail] using hout

end NearlyMinimax
