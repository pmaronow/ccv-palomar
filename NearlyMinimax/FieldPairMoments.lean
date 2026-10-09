module

public import NearlyMinimax.TwoStagePairRisk


@[expose] public section

/-! Actual joint second moments and means of the two-stage pair statistic. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω] [MeasurableSpace E]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

theorem fieldWeightedSymmetrization_memLp (weight : ℝ) {G : P → E × E → ℝ}
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ))) :
    MemLp (fun z : P × (E × E) => weightedSymmetrization weight (G z.1) z.2)
      2 (π.prod (μ.prod μ)) := by
  have hs : MeasurePreserving (fun z : P × (E × E) => (z.1, z.2.swap))
      (π.prod (μ.prod μ)) (π.prod (μ.prod μ)) :=
    (MeasurePreserving.id π).prod Measure.measurePreserving_swap
  exact (hG.add (hG.comp_measurePreserving hs)).const_mul (weight / 4)

theorem fieldPairAverage_memLp {n : ℕ} (weight : ℝ) {G : P → E × E → ℝ}
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    (X : Fin n → Ω → E) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ) :
    MemLp (fieldPairAverage n weight G X) 2 (π.prod ν) := by
  unfold fieldPairAverage
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  have hij := (Finset.mem_filter.mp hp).2
  have hm : MeasurePreserving (fun z : P × Ω => (z.1, (X p.1 z.2, X p.2 z.2)))
      (π.prod ν) (π.prod (μ.prod μ)) :=
    (MeasurePreserving.id π).prod (pair_measurePreserving X hind hX hij)
  exact (fieldWeightedSymmetrization_memLp weight hG).comp_measurePreserving hm

theorem fieldPairAverage_integral {n : ℕ} (hn : 2 ≤ n) (weight : ℝ)
    {G : P → E × E → ℝ}
    (hmG : Measurable (fun z : P × (E × E) => G z.1 z.2))
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    (X : Fin n → Ω → E) (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ) :
    (∫ z, fieldPairAverage n weight G X z ∂π.prod ν) =
      ∫ p, fieldPairMean (μ := μ) weight G p ∂π := by
  rw [integral_prod _ ((fieldPairAverage_memLp weight hG X hind hX).integrable (by norm_num))]
  apply integral_congr_ae
  filter_upwards [PilotFields.memLp_sections hG] with p hp
  have hm : Measurable (G p) := hmG.comp (measurable_const.prodMk measurable_id)
  exact (pairAverage_integral hn X hind hX
    (weightedSymmetrization_measurable weight hm) (weightedSymmetrization_memLp weight hp)).trans
      (weightedSymmetrization_mean weight hp)

end NearlyMinimax.PairUStatistic
