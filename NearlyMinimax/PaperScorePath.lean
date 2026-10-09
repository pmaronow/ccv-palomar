module

public import NearlyMinimax.MixtureRisk


@[expose] public section

/-! The manuscript's score-to-risk comparison for actual mixtures of the
original statistical experiment. The exceptional-state contribution and the
restriction to clipped estimators are consequences, not hypotheses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem paper_score_to_risk {Α : Type*} [MeasurableSpace Α] {d n : ℕ}
    (C : ModelConstants d) (σ : ℝ → Measure Α)
    (L : ℝ → Kernel Α (Fin n → Observation d))
    (θ : ℝ → Α → RegressionParameter d) (V : ℝ → ℝ)
    (R : ℝ → (Fin n → Observation d) → ℝ) (δ ε : ℝ) (hδ : 0 ≤ δ)
    (hσ : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (σ t))
    (hLprob : ∀ t ∈ Icc 0 δ, IsMarkovKernel (L t))
    (hL : ∀ t ∈ Icc 0 δ, ∀ a, L t a = sampleLaw (θ t a) n)
    (hVθ : ∀ t ∈ Icc 0 δ, ∀ a, (θ t a).variance = V t)
    (hV : ∀ t ∈ Icc 0 δ, V t ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : ℝ → Set Α) (hbad : ∀ t ∈ Icc 0 δ, MeasurableSet (bad t))
    (hlegal : ∀ t ∈ Icc 0 δ, ∀ a ∉ bad t, Admissible C (θ t a))
    (hmass : ∀ t ∈ Icc 0 δ, (σ t).real (bad t) ≤ ε)
    (hR : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → MemLp (R t) 2 (L t ∘ₘ σ t))
    (hcenter : ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      (∫ x, R t x ∂(L t ∘ₘ σ t)) = 0)
    (hAC : ∀ T : BoundedEstimator C n, AbsolutelyContinuousOnInterval
      (fun t => ∫ x, T.val.val x ∂(L t ∘ₘ σ t)) 0 δ)
    (hderiv : ∀ T : BoundedEstimator C n, ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      HasDerivAt (fun u => ∫ x, T.val.val x ∂(L u ∘ₘ σ u))
        (∫ x, T.val.val x * R t x ∂(L t ∘ₘ σ t)) t)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t))) volume 0 δ) :
    ENNReal.ofReal ((V δ - V 0) ^ 2 /
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t))) ^ 2
      - (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε) ≤ minimaxRisk C n := by
  have hε : 0 ≤ ε := (measureReal_nonneg).trans (hmass 0 ⟨le_rfl, hδ⟩)
  let P (t : ℝ) := L t ∘ₘ σ t
  have hprob (t : ℝ) (ht : t ∈ Icc 0 δ) : IsProbabilityMeasure (P t) := by
    let _ := hσ t ht
    let _ := hLprob t ht
    dsimp only [P]
    infer_instance
  rw [minimaxRisk_eq_inf_bounded]
  apply le_iInf
  intro T
  let risk := worstCaseRisk C T.val
  let D := effectiveVarianceUpper C - C.varianceLower
  let r := Real.sqrt (risk.toReal + D ^ 2 * ε)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrEq : r ^ 2 = risk.toReal + D ^ 2 * ε :=
    Real.sq_sqrt (add_nonneg ENNReal.toReal_nonneg (mul_nonneg (sq_nonneg _) hε))
  have hTrisk (t : ℝ) (ht : t ∈ Icc 0 δ) :
      (∫ x, (T.val.val x - V t) ^ 2 ∂P t) ≤ r ^ 2 := by
    let _ := hσ t ht
    let _ := hLprob t ht
    rw [hrEq]
    exact boundedEstimator_mixture_risk_le_of_exceptional_set C T (σ t) (L t) (θ t) (V t) ε
      (hL t ht) (hVθ t ht) (hV t ht) (bad t) (hbad t ht) (hlegal t ht) (hmass t ht)
  have hT (t : ℝ) (ht : t ∈ Icc 0 δ) : MemLp T.val.val 2 (P t) := by
    let _ := hprob t ht
    exact boundedEstimator_memLp C T (P t) 2
  have hlower := probability_absolutelyContinuous_score_path_risk_lower_bound
    P T.val.val R V δ r risk.toReal D ε hδ hr hprob hT hR hcenter (hAC T)
    (hderiv T) hTrisk hscoreInt hrEq
  have h := ENNReal.ofReal_le_ofReal hlower
  simpa only [P, D, risk, ENNReal.ofReal_toReal
    (boundedEstimator_worstCaseRisk_finite C T).ne] using h

end NearlyMinimax
