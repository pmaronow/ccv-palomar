module

public import NearlyMinimax.PaperLowerSharp
public import NearlyMinimax.PaperSharpUpper
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.NatRateConsequences


@[expose] public section

/-! The paper's main bracket and unconditional asymptotic consequences.
The statistical upper and lower bounds used here are proved for the original
model, with constants uniform over the open extension domain. -/

noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

theorem paper_main {d : ℕ} (C : ModelConstants d) : MainBracketClaim C :=
  mainBracketClaim_of_separate_bounds C (paper_upper_sharp C) (paper_lower_sharp C)

theorem paper_exponent_limit {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    Tendsto (fun n : ℕ => -Real.log (minimaxRMS C n).toReal / Real.log (n : ℝ))
      atTop (𝓝 (rateExponent C.smoothness d)) :=
  paper_exponent_limit_of_mainBracketClaim C hreg (paper_main C)

theorem paper_polynomial_bounds {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*(n : ℝ)^(-rateExponent C.smoothness d-epsilon) ≤ (minimaxRMS C n).toReal ∧
        (minimaxRMS C n).toReal ≤ A*(n : ℝ)^(-rateExponent C.smoothness d) :=
  polynomial_bounds_nat_of_rateBracket (paper_stretchConstant_pos C hreg)
    (hasNatRateBracket_of_mainBracketClaim C hreg (paper_main C))

theorem paper_stretch_limit {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    Tendsto (fun n : ℕ =>
      (Real.log (minimaxRMS C n).toReal + rateExponent C.smoothness d * Real.log n) /
        Real.sqrt (Real.log n)) atTop
      (𝓝 (-stretchConstant C.smoothness d (paperTau C))) :=
  paper_stretch_limit_of_mainBracketClaim C hreg (paper_main C)

theorem paper_log_expansion {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |Real.log (minimaxRMS C n).toReal + rateExponent C.smoothness d * Real.log n +
        stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)|
          ≤ K * Real.log (Real.log n) :=
  paper_log_expansion_of_mainBracketClaim C hreg (paper_main C)

theorem paper_normalized_risk_tends_zero {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    Tendsto (fun n : ℕ => (n : ℝ)^(rateExponent C.smoothness d)*(minimaxRMS C n).toReal)
      atTop (𝓝 0) :=
  normalized_risk_tends_zero_nat_of_rateBracket (paper_stretchConstant_pos C hreg)
    (hasNatRateBracket_of_mainBracketClaim C hreg (paper_main C))

end NearlyMinimax
