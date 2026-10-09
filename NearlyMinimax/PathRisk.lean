module

public import NearlyMinimax.Risk


@[expose] public section

/-! Score-to-risk comparison on arbitrary measurable observation spaces.
The density path and its observable derivative are input data; no risk lower
bound is assumed.  This proves the comparison for pointwise differentiable
means.  The manuscript's weaker absolutely-continuous, almost-everywhere
formulation remains a separate obligation.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax

theorem probability_score_path_separation_le {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (T : Ω → ℝ) (R : ℝ → Ω → ℝ) (V : ℝ → ℝ)
    (δ r : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hprob : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (P t))
    (hT : ∀ t ∈ Icc 0 δ, MemLp T 2 (P t))
    (hR : ∀ t ∈ Icc 0 δ, MemLp (R t) 2 (P t))
    (hcenter : ∀ t ∈ Icc 0 δ, (∫ x, R t x ∂P t) = 0)
    (hderiv : ∀ t ∈ Icc 0 δ,
      HasDerivAt (fun u => ∫ x, T x ∂P u) (∫ x, T x * R t x ∂P t) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∫ x, (T x - V t) ^ 2 ∂P t) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) volume 0 δ)
    (hderivInt : IntervalIntegrable
      (fun t => ∫ x, T x * R t x ∂P t) volume 0 δ) :
    |V δ - V 0| ≤
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) * r := by
  apply path_separation_le hδ hderiv hderivInt hscoreInt
  · intro t ht
    let _ := hprob t ht
    exact probability_score_bound (P t) T (R t) (V t) r
      (hT t ht) (hR t ht) hr (hcenter t ht) (hrisk t ht)
  · let _ := hprob 0 ⟨le_rfl, hδ⟩
    exact probability_mean_error_le (P 0) T (V 0) r
      (hT 0 ⟨le_rfl, hδ⟩) hr (hrisk 0 ⟨le_rfl, hδ⟩)
  · let _ := hprob δ ⟨hδ, le_rfl⟩
    exact probability_mean_error_le (P δ) T (V δ) r
      (hT δ ⟨hδ, le_rfl⟩) hr (hrisk δ ⟨hδ, le_rfl⟩)

/-- Exceptional latent states cost at most the squared clipping diameter
times their probability, on an arbitrary probability space. -/
theorem probability_mixture_exceptional_risk_bound {Α : Type*} [MeasurableSpace Α]
    (μ : Measure Α) [IsProbabilityMeasure μ] (e : Α → ℝ)
    (bad : Set Α) (hbadmeas : MeasurableSet bad) (risk D ε : ℝ)
    (he : Integrable e μ) (hrisk : 0 ≤ risk)
    (hgood : ∀ᵐ x ∂μ, x ∉ bad → e x ≤ risk)
    (hbad : ∀ᵐ x ∂μ, x ∈ bad → e x ≤ D ^ 2)
    (hmass : μ.real bad ≤ ε) :
    (∫ x, e x ∂μ) ≤ risk + D ^ 2 * ε := by
  have hI : Integrable (bad.indicator (fun _ : Α => D ^ 2)) μ :=
    (integrable_const _).indicator hbadmeas
  have hp : e ≤ᵐ[μ] fun x => risk + bad.indicator (fun _ : Α => D ^ 2) x := by
    filter_upwards [hgood, hbad] with x hxgood hxbad
    by_cases hx : x ∈ bad
    · rw [indicator_of_mem hx]
      linarith [hxbad hx]
    · rw [indicator_of_notMem hx, add_zero]
      exact hxgood hx
  calc
    (∫ x, e x ∂μ) ≤ ∫ x, risk + bad.indicator (fun _ : Α => D ^ 2) x ∂μ :=
      integral_mono_ae he ((integrable_const _).add hI) hp
    _ = risk + D ^ 2 * μ.real bad := by
      rw [integral_add (integrable_const _) hI, integral_indicator hbadmeas,
        integral_const, integral_const]
      simp [Measure.real, mul_comm]
    _ ≤ risk + D ^ 2 * ε := by gcongr

theorem probability_score_path_risk_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (T : Ω → ℝ) (R : ℝ → Ω → ℝ) (V : ℝ → ℝ)
    (δ r risk D ε : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hprob : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (P t))
    (hT : ∀ t ∈ Icc 0 δ, MemLp T 2 (P t))
    (hR : ∀ t ∈ Icc 0 δ, MemLp (R t) 2 (P t))
    (hcenter : ∀ t ∈ Icc 0 δ, (∫ x, R t x ∂P t) = 0)
    (hderiv : ∀ t ∈ Icc 0 δ,
      HasDerivAt (fun u => ∫ x, T x ∂P u) (∫ x, T x * R t x ∂P t) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∫ x, (T x - V t) ^ 2 ∂P t) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) volume 0 δ)
    (hderivInt : IntervalIntegrable
      (fun t => ∫ x, T x * R t x ∂P t) volume 0 δ)
    (hriskEq : r ^ 2 = risk + D ^ 2 * ε) :
    (V δ - V 0) ^ 2 /
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) ^ 2
      - D ^ 2 * ε ≤ risk := by
  have hsep := probability_score_path_separation_le P T R V δ r hδ hr
    hprob hT hR hcenter hderiv hrisk hscoreInt hderivInt
  have hB : 0 ≤ ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t) :=
    intervalIntegral.integral_nonneg_of_forall hδ (fun t => Real.sqrt_nonneg _)
  simpa only [sq_abs] using
    path_risk_lower_bound hB hr (abs_nonneg (V δ - V 0)) hsep hriskEq

end NearlyMinimax
