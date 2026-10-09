module

public import NearlyMinimax.LowSmoothnessPrior
public import NearlyMinimax.Clipping


@[expose] public section

/-! The actual ternary neighborhood lies in the effective original
variance interval, including the fourth-moment cap. -/
noncomputable section
open Set
namespace NearlyMinimax

 theorem LowSmoothnessTernaryConstants.effective_interval {d : ℕ}
    {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C)
    {V : ℝ} (hV : |V-Q.v| ≤ Q.ρ) : V ∈ Icc C.varianceLower (effectiveVarianceUpper C) := by
  have h := Q.legal 0 V (by simpa using Q.ρ_pos.le) hV
  have hp := Q.c_pos.trans_le (h.2.2.1 1)
  have hp' : 0 < 1 - V / Q.a^2 := by simpa [ternaryMass] using hp
  have hVa : V < Q.a^2 := (div_lt_one (sq_pos_of_pos Q.a_pos)).mp (by linarith)
  have hfourth : Q.a^2*V ≤ C.fourthBound := by
    have hf := h.2.2.2
    rw [ternary_fourth_central_moment Q.a 0 V Q.a_pos.ne'] at hf
    simpa using hf
  obtain ⟨θ,hθ,hθV⟩ := uniformZeroParameter_admissible C Q.a V Q.a_pos h.1.le h.2.1.le hVa hfourth
  simpa only [hθV,effectiveVarianceUpper] using admissible_variance_effective_interval C θ hθ

end NearlyMinimax
