module

public import NearlyMinimax.WeightedPair
public import NearlyMinimax.TwoStageRisk
public import NearlyMinimax.PilotFields


@[expose] public section

/-! Averaged evaluation risk of an actual two-stage pair statistic. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {P Ω E I : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

def fieldPairAverage (n : ℕ) (weight : ℝ) (G : P → E × E → ℝ)
    (X : Fin n → Ω → E) (z : P × Ω) : ℝ :=
  pairAverage n (weightedSymmetrization weight (G z.1)) (fun i => X i z.2)

theorem fieldPairAverage_measurable (n : ℕ) (weight : ℝ) {G : P → E × E → ℝ}
    (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2))
    (X : Fin n → Ω → E) (hX : ∀ i, Measurable (X i)) :
    Measurable (fieldPairAverage n weight G X) := by
  unfold fieldPairAverage pairAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  unfold weightedSymmetrization
  apply Measurable.const_mul
  exact (hmG.comp (measurable_fst.prodMk
    (((hX i).comp measurable_snd).prodMk ((hX j).comp measurable_snd)))).add
      (hmG.comp (measurable_fst.prodMk
        (((hX j).comp measurable_snd).prodMk ((hX i).comp measurable_snd))))

def fieldPairMean (weight : ℝ) (G : P → E × E → ℝ) (p : P) : ℝ :=
  weight / 2 * ∫ z, G p z ∂μ.prod μ

theorem fieldPairMean_measurable (weight : ℝ) {G : P → E × E → ℝ}
    (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2)) :
    Measurable (fieldPairMean (μ := μ) weight G) :=
  hmG.stronglyMeasurable.integral_prod_right'.measurable.const_mul _

theorem fieldPairAverage_two_stage_mse_le {n : ℕ} (hn : 2 ≤ n)
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
    (hmean : (∫⁻ p, ENNReal.ofReal ((fieldPairMean (μ := μ) weight G p - c) ^ 2) ∂π) ≤
      ENNReal.ofReal d) :
    (∫⁻ z, ENNReal.ofReal ((fieldPairAverage n weight G X z - c) ^ 2) ∂π.prod ν) ≤
      ENNReal.ofReal (2 *
        (bound / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) *
        (weight * ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ)) + 2 * d) := by
  let a : ℝ := bound / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))
  let b : P → ℝ := fun p => weight * ∫ z, G p z ^ 2 ∂μ.prod μ
  have hb : Integrable b π := hG.integrable_sq.integral_prod_left.const_mul weight
  have hb0 : ∀ᵐ p ∂π, 0 ≤ b p := Filter.Eventually.of_forall (fun p =>
    mul_nonneg hw.le (integral_nonneg (fun _ => sq_nonneg _)))
  have hbn : 0 ≤ bound := (mul_nonneg hw.le hcap).trans hbound
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : ∀ᵐ p ∂π, (∫⁻ x, ENNReal.ofReal
      ((fieldPairAverage n weight G X (p, x) - fieldPairMean (μ := μ) weight G p) ^ 2) ∂ν) ≤
      ENNReal.ofReal (a * b p) := by
    filter_upwards [PilotFields.memLp_sections hG] with p hp
    have hmGp : Measurable (G p) := hmG.comp (measurable_const.prodMk measurable_id)
    have hT : MemLp (fun x => fieldPairAverage n weight G X (p, x) -
        fieldPairMean (μ := μ) weight G p) 2 ν :=
      (pairAverage_memLp_two X hind hX (weightedSymmetrization_memLp weight hp)).sub (memLp_const _)
    rw [← ofReal_integral_eq_lintegral_ofReal hT.integrable_sq
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_mono (weighted_pair_centered_sq_le hn X hind hX label hlabel
      hmGp hp (hsupport p) hw hcap hmass hbound)
  have hr := NearlyMinimax.two_stage_mean_squared_bound π ν
    (fieldPairAverage n weight G X) (fieldPairMean (μ := μ) weight G) b
    (fieldPairAverage_measurable n weight hmG X (fun i => (hX i).measurable))
    (fieldPairMean_measurable weight hmG) hb hb0 ha hd hc hmean
  have he : (∫ p, b p ∂π) = weight * ∫ z : P × (E × E), G z.1 z.2 ^ 2 ∂π.prod (μ.prod μ) := by
    rw [integral_const_mul, integral_prod _ hG.integrable_sq]
  simpa only [he, a] using hr

end NearlyMinimax.PairUStatistic
