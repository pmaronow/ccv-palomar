module

public import NearlyMinimax.CompleteSourceSaddleParameters
public import NearlyMinimax.LowerPenaltyReduction
public import NearlyMinimax.PaperGoals


@[expose] public section

/-! Numerical ending of the true complete-source cost construction. The
hypotheses are actual activity and primitive energy caps, never a desired
statistical rate or minimax conclusion. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem completeSourceSaddle_penalized_numeric_envelope {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf CB C5 C6 C7 ch ctr cm Cω : ℝ}
    (hcf : 0 < cf) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch) (hctr : 0 < ctr) (hcm : 0 < cm)
    (hshift : 1+Real.log (rawCostConstant CB C5 C6 C7 cf ch)+
      ((d : ℝ)^2-16*C.smoothness)/((d : ℝ)*((d : ℝ)+4))*highCompleteSourceSaddleTheta C+
      2*d*densityIntervalExponent C.densityLower C.densityUpper/((d : ℝ)+4) < Cω) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let tauM := shrunkDensityExponent C.densityLower C.densityUpper
      let k := lowerSaddleGrid d m theta Cω n
      let eta := cf*(k : ℝ)^(-C.smoothness)
      let B := lowerSaddleActivity C.smoothness d m theta Cω tauM n
      ∀ Bl E : ℝ, 1 ≤ B → 0 ≤ Bl → 0 ≤ E → Bl ≤ CB*B →
      E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf C5 C6 C7 ch Bl tauM n →
      (c*paperRiskScale C n)^2 ≤ ctr*eta^4/(1+Bl^2+(k : ℝ)^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2*highCompleteSourceSaddleTail C Cω cm n := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let CG := rawCostConstant CB C5 C6 C7 cf ch
  have hCG : 0 < CG := lt_of_lt_of_le zero_lt_one (rawCostConstant_ge_one _ _ _ _ _ _)
  have hmgf := highHistoryMassMomentConstant_pos d C.densityLower C.densityUpper hab
  obtain ⟨c,hc,hpen⟩ := eventually_actual_lowerSaddle_penalized_rate_square
    hs hd C.densityLower_pos hab hcf hCG hctr hcm hmgf Cω
  have hcost := eventually_actual_lowerSaddle_raw_cost hs hd C.densityLower_pos hab
    hcf.le hCB hC5 hC6 hC7 hch hshift
  refine ⟨c,hc,?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hpen,
    tendsto_natCast_atTop_atTop.eventually hcost,eventually_ge_atTop (2 : ℕ)] with n hn hcst hn2
  dsimp only at hn hcst ⊢
  intro Bl E hB hBl hE hBlcap hEcap
  have hden := hcst Bl E hB hBl hBlcap hEcap
  have hvolume := completeSourceSaddle_inverse_volume C Cω (n : ℝ)
  have hdenpos : 0 < 1+Bl^2+
      (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d*E := by positivity
  have hcost' : 1+Bl^2+
      (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d*E ≤
      3*CG*(lowerSaddleActivity C.smoothness d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) n)^2 := by
    rw [hvolume]
    exact hden
  have hmain := lowerSaddle_cost_risk_reduction (cf := cf)
    (shrunkDensityExponent C.densityLower C.densityUpper) hdenpos hCG hctr.le hcost'
  rw [← completeSourceSaddle_eta_eq C Cω cf (n : ℝ)] at hmain
  have hpaper : paperRiskScale C n =
      rateScale (rateExponent C.smoothness d)
        (stretchConstant C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper))
        (lowerLogPower C.smoothness d) n := paperRiskScale_eq_rateScale C hn2
  rw [hpaper]
  apply hn.trans
  exact sub_le_sub_right hmain _

end NearlyMinimax
