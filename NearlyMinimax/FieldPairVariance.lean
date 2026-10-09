module

public import NearlyMinimax.FieldPairMoments


@[expose] public section

/-! Joint Bochner variance bounds with integrability derived from genuine
independent sample observations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {P Ω E I : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

theorem fieldPairAverage_centered_sq_le {n : ℕ} (hn : 2 ≤ n)
    (X : Fin n → Ω → E) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ)
    (label : E → I) (hlabel : Measurable label)
    {G : P → E × E → ℝ}
    (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2))
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    (hsupport : ∀ p x y, label x ≠ label y → G p (x, y) = 0)
    {weight cap bound d c : ℝ} (hw : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) (hbound : weight * cap ≤ bound)
    (hd : 0 ≤ d)
    (hmean2 : MemLp (fieldPairMean (μ := μ) weight G) 2 π)
    (hmean : (∫ p, (fieldPairMean (μ := μ) weight G p - c) ^ 2 ∂π) ≤ d) :
    (∫ z, (fieldPairAverage n weight G X z - c) ^ 2 ∂π.prod ν) ≤
      2 * (bound / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) *
        (weight * ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ)) + 2 * d := by
  have hmeanC : MemLp (fun p => fieldPairMean (μ := μ) weight G p - c) 2 π :=
    hmean2.sub (memLp_const c)
  have hfieldC : MemLp (fun z => fieldPairAverage n weight G X z - c) 2 (π.prod ν) :=
    (fieldPairAverage_memLp weight hG X hind hX).sub (memLp_const c)
  have hm : (∫⁻ p, ENNReal.ofReal ((fieldPairMean (μ := μ) weight G p - c) ^ 2) ∂π) ≤
      ENNReal.ofReal d := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      hmeanC.integrable_sq
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_mono hmean
  have hr := fieldPairAverage_two_stage_mse_le hn X hind hX label hlabel hmG hG
    hsupport hw hcap hmass hbound hd hm
  rw [← ofReal_integral_eq_lintegral_ofReal
    hfieldC.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at hr
  have hbn : 0 ≤ bound := (mul_nonneg hw.le hcap).trans hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by
    have he : 0 ≤ ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ) :=
      integral_nonneg (fun _ => sq_nonneg _)
    positivity)).1 hr

end NearlyMinimax.PairUStatistic
