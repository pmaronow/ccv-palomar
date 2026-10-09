module

public import NearlyMinimax.PaperScorePath


@[expose] public section

/-! The score comparison with the manuscript's original variance interval.
If a path leaves the effective interval enforced by the fourth-moment cap,
all its states are exceptional at that time and the stated bound is trivial. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem paper_score_to_risk_original_interval {Α : Type*} [MeasurableSpace Α] {d n : ℕ}
    (C : ModelConstants d) (σ : ℝ → Measure Α)
    (L : ℝ → Kernel Α (Fin n → Observation d))
    (θ : ℝ → Α → RegressionParameter d) (V : ℝ → ℝ)
    (R : ℝ → (Fin n → Observation d) → ℝ) (δ ε : ℝ) (hδ : 0 ≤ δ)
    (hσ : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (σ t))
    (hLprob : ∀ t ∈ Icc 0 δ, IsMarkovKernel (L t))
    (hL : ∀ t ∈ Icc 0 δ, ∀ a, L t a = sampleLaw (θ t a) n)
    (hVθ : ∀ t ∈ Icc 0 δ, ∀ a, (θ t a).variance = V t)
    (hV : ∀ t ∈ Icc 0 δ, V t ∈ Icc C.varianceLower C.varianceUpper)
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
      - (C.varianceUpper - C.varianceLower) ^ 2 * ε) ≤ minimaxRisk C n := by
  classical
  have hε : 0 ≤ ε := measureReal_nonneg.trans (hmass 0 ⟨le_rfl, hδ⟩)
  by_cases heff : ∀ t ∈ Icc 0 δ,
      V t ∈ Icc C.varianceLower (effectiveVarianceUpper C)
  · have hbase := paper_score_to_risk C σ L θ V R δ ε hδ hσ hLprob hL hVθ heff
      bad hbad hlegal hmass hR hcenter hAC hderiv hscoreInt
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbase
    have hlow : 0 ≤ effectiveVarianceUpper C - C.varianceLower :=
      sub_nonneg.mpr (effective_variance_interval_nondegenerate C).le
    have hupp : effectiveVarianceUpper C ≤ C.varianceUpper := min_le_left _ _
    have hsq : (effectiveVarianceUpper C - C.varianceLower) ^ 2 ≤
        (C.varianceUpper - C.varianceLower) ^ 2 := by nlinarith only [hlow, hupp]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right hsq hε) _
  · push Not at heff
    obtain ⟨t, ht, hnot⟩ := heff
    have hbadAll : bad t = univ := by
      apply Set.eq_univ_of_forall
      intro a
      by_contra ha
      have hv := admissible_variance_effective_interval C (θ t a) (hlegal t ht a ha)
      rw [hVθ t ht a] at hv
      exact hnot hv
    have hεone : 1 ≤ ε := by
      let _ := hσ t ht
      simpa [hbadAll, measureReal_def] using hmass t ht
    have hV0 := hV 0 ⟨le_rfl, hδ⟩
    have hVδ := hV δ ⟨hδ, le_rfl⟩
    have hnum : (V δ - V 0) ^ 2 ≤ (C.varianceUpper - C.varianceLower) ^ 2 := by
      nlinarith only [hV0.1, hV0.2, hVδ.1, hVδ.2,
        sq_nonneg (C.varianceUpper - V δ + V 0 - C.varianceLower),
        sq_nonneg (C.varianceUpper + V δ - V 0 - C.varianceLower)]
    have hint : 0 ≤ ∫ t in (0 : ℝ)..δ,
        Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t)) :=
      intervalIntegral.integral_nonneg_of_forall hδ (fun _ => Real.sqrt_nonneg _)
    have hden : 1 ≤ (2 + ∫ t in (0 : ℝ)..δ,
        Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t))) ^ 2 := by
      nlinarith only [hint, sq_nonneg (∫ t in (0 : ℝ)..δ,
        Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t)))]
    have hratio := (div_le_self (sq_nonneg (V δ - V 0)) hden).trans hnum
    have hpenalty : (C.varianceUpper - C.varianceLower) ^ 2 ≤
        (C.varianceUpper - C.varianceLower) ^ 2 * ε := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hεone (sq_nonneg (C.varianceUpper - C.varianceLower))
    rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (hratio.trans hpenalty))]
    exact bot_le

end NearlyMinimax
