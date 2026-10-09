module

public import NearlyMinimax.CompleteSaddleNumericalReduction
public import NearlyMinimax.LowerRMSAlgebra


@[expose] public section

/-! Exact ending of the complete-source lower construction. This module
turns the actual raw-energy cost and exceptional-mass estimate into the
paper's root-risk scale. Its premise is the intermediate constructed cost,
not an assumed target rate. -/
noncomputable section
open Filter
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def CompleteSaddleCostRiskBudget {d : ℕ} (C : ModelConstants d)
    (cf CB C5 C6 C7 ch ctr cm Cω : ℝ) (n : ℕ) : Prop :=
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tauM := shrunkDensityExponent C.densityLower C.densityUpper
  let k := lowerSaddleGrid d m theta Cω n
  let eta := cf*(k : ℝ)^(-C.smoothness)
  let B := lowerSaddleActivity C.smoothness d m theta Cω tauM n
  ∃ Bl E : ℝ, 1 ≤ B ∧ 0 ≤ Bl ∧ 0 ≤ E ∧ Bl ≤ CB*B ∧
    E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf C5 C6 C7 ch Bl tauM n ∧
    ∀ U : ExtensionDomain d,
      ENNReal.ofReal (ctr*eta^4/(1+Bl^2+(k : ℝ)^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2*highCompleteSourceSaddleTail C Cω cm n) ≤
        minimaxRisk (C.withDomain U) n

/-- Fixed constants for the primitive raw cost precede the saddle shift,
the extension domain and the sample size. -/
theorem completeSaddle_lower_rate_of_actual_cost_budget {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf CB C5 C6 C7 ch ctr cm : ℝ}
    (hcf : 0 < cf) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch) (hctr : 0 < ctr) (hcm : 0 < cm)
    (hcost : ∀ Cω : ℝ, ∀ᶠ n : ℕ in atTop,
      CompleteSaddleCostRiskBudget C cf CB C5 C6 C7 ch ctr cm Cω n) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        ENNReal.ofReal (c*paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n := by
  let Cω := 1+Real.log (rawCostConstant CB C5 C6 C7 cf ch)+
    ((d : ℝ)^2-16*C.smoothness)/((d : ℝ)*((d : ℝ)+4))*highCompleteSourceSaddleTheta C+
    2*d*densityIntervalExponent C.densityLower C.densityUpper/((d : ℝ)+4)+1
  obtain ⟨c,hc,hrate⟩ := completeSourceSaddle_penalized_numeric_envelope C hs hd
    hcf hCB hC5 hC6 hC7 hch hctr hcm (Cω := Cω) (by dsimp only [Cω]; linarith)
  have hall : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ ∀ U : ExtensionDomain d,
        ENNReal.ofReal (c*paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n := by
    filter_upwards [hcost Cω,hrate,eventually_ge_atTop (2 : ℕ)] with n hcostn hraten hn
    rcases hcostn with ⟨Bl,E,hB,hBl,hE,hBlcap,hEcap,hrisk⟩
    refine ⟨hn,fun U => ?_⟩
    apply minimaxRMS_lower_of_squared_lower (C.withDomain U)
      (mul_pos hc (paperRiskScale_pos C hn)).le
    exact (ENNReal.ofReal_le_ofReal (hraten Bl E hB hBl hE hBlcap hEcap)).trans (hrisk U)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hall
  exact ⟨c,hc,n₀,(hn₀ n₀ le_rfl).1,fun U n hn => (hn₀ n hn).2 U⟩

end NearlyMinimax
