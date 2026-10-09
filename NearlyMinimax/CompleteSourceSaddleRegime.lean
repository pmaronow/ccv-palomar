module

public import NearlyMinimax.CompleteSourceSaddleParameters
public import NearlyMinimax.SourceSaddleHigherSelection


@[expose] public section

/-! Fixed regularity and physical higher-row guards at the actual natural
sample sequence. These are consequences of the rounded saddle definitions. -/
noncomputable section
open Filter
namespace NearlyMinimax

 theorem completeSourceSaddle_fixed_regime_window {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf : ℝ} (hcf : 0 < cf) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (Cω eta0 : ℝ) (M0 : ℕ), 0 < eta0 →
      ∀ᶠ n : ℕ in atTop,
        LowerSaddleReg K eta0 C.smoothness d (highCompleteSourceSaddleCoefficient C)
          (highCompleteSourceSaddleTheta C) Cω cf M0
          (shrunkDensityExponent C.densityLower C.densityUpper) n := by
  obtain ⟨K,hK,h⟩ := actual_lowerSaddle_fixed_regime_window hs hd C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hcf
  refine ⟨K,hK,fun Cω eta0 M0 heta0 => ?_⟩
  exact tendsto_natCast_atTop_atTop.eventually (h Cω eta0 M0 heta0)

 theorem completeSourceSaddle_response_order_ge_two {d : ℕ} (C : ModelConstants d) :
    2 ≤ lowerSaddleResponseOrder C.smoothness d := le_max_left _ _

 theorem completeSourceSaddle_higher_family_eventually_legal {d : ℕ}
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ)) (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let M := lowerSaddleM m n
      let N := lowerSaddleN C.smoothness d m theta Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) n
      let mu := lowerSaddleMu d m theta Cω n
      let ell := lowerAliasCutoff C.smoothness d m theta Cω
        (densityIntervalExponent C.densityLower C.densityUpper+1)
        (shrunkDensityExponent C.densityLower C.densityUpper) n
      1 ≤ ell ∧ (∀ r : ℕ, 0 < higherBandTargetScale d r N mu) ∧
        (∀ r : ℕ, ell < higherBandTargetScale d r N mu → r ≤ M) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (sourceSaddleHigherFamily_eventually_legal d C.smoothness C.densityLower C.densityUpper Cω
      hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper))

end NearlyMinimax
