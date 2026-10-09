module

public import NearlyMinimax.PaperGoals
public import NearlyMinimax.Chebyshev


@[expose] public section

/-! The paper's numerical constants and conditional analytic corollaries.
The results involving minimax rates explicitly assume `MainBracketClaim`.
-/

noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

theorem paperTau_pos {d : ℕ} (C : ModelConstants d) : 0 < paperTau C := by
  have hab : C.densityLower < C.densityUpper :=
    C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hs : Real.sqrt C.densityLower < Real.sqrt C.densityUpper :=
    Real.sqrt_lt_sqrt C.densityLower_pos.le hab
  have hl : 0 < Real.sqrt C.densityLower := Real.sqrt_pos.mpr C.densityLower_pos
  apply Real.log_pos
  apply (one_lt_div (sub_pos.mpr hs)).mpr
  linarith

theorem exp_neg_paperTau {d : ℕ} (C : ModelConstants d) :
    Real.exp (-paperTau C) =
      (Real.sqrt C.densityUpper - Real.sqrt C.densityLower) /
        (Real.sqrt C.densityUpper + Real.sqrt C.densityLower) := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have h := exp_neg_exteriorTau C.densityLower C.densityUpper C.densityLower_pos hab
  rw [exteriorTau_sqrt_ratio C.densityLower C.densityUpper C.densityLower_pos hab] at h
  exact h

theorem paper_stretchConstant_pos {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    0 < stretchConstant C.smoothness d (paperTau C) :=
  stretchConstant_pos hreg.1 hreg.2 (paperTau_pos C)

theorem paper_conjecturedExponent_gap {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    rateExponent C.smoothness d < 4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness) :=
  rateExponent_lt_conjectured hreg.1 hreg.2

theorem paper_fixedDesignExponent_gap {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    2 * C.smoothness / (d : ℝ) < rateExponent C.smoothness d :=
  fixedDesignExponent_lt_rate hreg.1 hreg.2

/-- Conditional recovery of the common stretched-exponential constant. -/
theorem paper_stretch_limit_of_mainBracketClaim {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hmain : MainBracketClaim C) :
    Tendsto (fun n : ℕ =>
      (Real.log (minimaxRMS C n).toReal + rateExponent C.smoothness d * Real.log n) /
        Real.sqrt (Real.log n)) atTop
      (𝓝 (-stretchConstant C.smoothness d (paperTau C))) :=
  stretch_constant_limit_nat_of_rateBracket
    (hasNatRateBracket_of_mainBracketClaim C hreg hmain)

/-- Conditional logarithmic expansion, with an explicit eventual error bound. -/
theorem paper_log_expansion_of_mainBracketClaim {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hmain : MainBracketClaim C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |Real.log (minimaxRMS C n).toReal + rateExponent C.smoothness d * Real.log n +
        stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)|
          ≤ K * Real.log (Real.log n) :=
  log_expansion_nat_of_rateBracket
    (hasNatRateBracket_of_mainBracketClaim C hreg hmain)

end NearlyMinimax
