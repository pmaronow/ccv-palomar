module

public import NearlyMinimax.PathRisk
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun


@[expose] public section

/-! Score-to-risk comparison with the manuscript's absolutely continuous
observable means and almost-everywhere score identity. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem absolutelyContinuous_path_mean_change_le {m score : ℝ → ℝ} {δ r : ℝ}
    (hδ : 0 ≤ δ) (hAC : AbsolutelyContinuousOnInterval m 0 δ)
    (hscore : IntervalIntegrable score volume 0 δ)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → |deriv m t| ≤ r * score t) :
    |m δ - m 0| ≤ r * ∫ t in (0 : ℝ)..δ, score t := by
  rw [← hAC.integral_deriv_eq_sub, ← intervalIntegral.integral_const_mul]
  apply (show ‖∫ t in (0 : ℝ)..δ, deriv m t‖ ≤ _ from
    intervalIntegral.norm_integral_le_of_norm_le hδ ?_ (hscore.const_mul r))
  filter_upwards [hbound] with t ht hmem
  exact ht ⟨hmem.1.le, hmem.2⟩

theorem absolutelyContinuous_path_separation_le {m score : ℝ → ℝ} {δ r V₀ Vδ : ℝ}
    (hδ : 0 ≤ δ) (hAC : AbsolutelyContinuousOnInterval m 0 δ)
    (hscore : IntervalIntegrable score volume 0 δ)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → |deriv m t| ≤ r * score t)
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + ∫ t in (0 : ℝ)..δ, score t) * r := by
  have hchange := absolutelyContinuous_path_mean_change_le hδ hAC hscore hbound
  calc
    |Vδ - V₀| = |(Vδ - m δ) + (m δ - m 0) + (m 0 - V₀)| := by congr 1; ring
    _ ≤ |Vδ - m δ| + |m δ - m 0| + |m 0 - V₀| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ r + (r * ∫ t in (0 : ℝ)..δ, score t) + r := by
      rw [abs_sub_comm Vδ (m δ)]
      exact add_le_add (add_le_add hlast hchange) hfirst
    _ = _ := by ring

/-- The score and derivative are only required almost everywhere in time. -/
theorem probability_absolutelyContinuous_score_path_separation_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (T : Ω → ℝ) (R : ℝ → Ω → ℝ) (V : ℝ → ℝ)
    (δ r : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hprob : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (P t))
    (hT : ∀ t ∈ Icc 0 δ, MemLp T 2 (P t))
    (hR : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → MemLp (R t) 2 (P t))
    (hcenter : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → (∫ x, R t x ∂P t) = 0)
    (hAC : AbsolutelyContinuousOnInterval (fun t => ∫ x, T x ∂P t) 0 δ)
    (hderiv : ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      HasDerivAt (fun u => ∫ x, T x ∂P u) (∫ x, T x * R t x ∂P t) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∫ x, (T x - V t) ^ 2 ∂P t) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) volume 0 δ) :
    |V δ - V 0| ≤
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) * r := by
  apply absolutelyContinuous_path_separation_le hδ hAC hscoreInt
  · filter_upwards [hR, hcenter, hderiv] with t hRt hct hdt ht
    let _ := hprob t ht
    rw [(hdt ht).deriv]
    exact probability_score_bound (P t) T (R t) (V t) r
      (hT t ht) (hRt ht) hr (hct ht) (hrisk t ht)
  · let _ := hprob 0 ⟨le_rfl, hδ⟩
    exact probability_mean_error_le (P 0) T (V 0) r
      (hT 0 ⟨le_rfl, hδ⟩) hr (hrisk 0 ⟨le_rfl, hδ⟩)
  · let _ := hprob δ ⟨hδ, le_rfl⟩
    exact probability_mean_error_le (P δ) T (V δ) r
      (hT δ ⟨hδ, le_rfl⟩) hr (hrisk δ ⟨hδ, le_rfl⟩)

theorem probability_absolutelyContinuous_score_path_risk_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (T : Ω → ℝ) (R : ℝ → Ω → ℝ) (V : ℝ → ℝ)
    (δ r risk D ε : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hprob : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (P t))
    (hT : ∀ t ∈ Icc 0 δ, MemLp T 2 (P t))
    (hR : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → MemLp (R t) 2 (P t))
    (hcenter : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → (∫ x, R t x ∂P t) = 0)
    (hAC : AbsolutelyContinuousOnInterval (fun t => ∫ x, T x ∂P t) 0 δ)
    (hderiv : ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      HasDerivAt (fun u => ∫ x, T x ∂P u) (∫ x, T x * R t x ∂P t) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∫ x, (T x - V t) ^ 2 ∂P t) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) volume 0 δ)
    (hriskEq : r ^ 2 = risk + D ^ 2 * ε) :
    (V δ - V 0) ^ 2 /
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) ^ 2
      - D ^ 2 * ε ≤ risk := by
  have hsep := probability_absolutelyContinuous_score_path_separation_le P T R V δ r hδ hr
    hprob hT hR hcenter hAC hderiv hrisk hscoreInt
  have hB : 0 ≤ ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t) :=
    intervalIntegral.integral_nonneg_of_forall hδ (fun t => Real.sqrt_nonneg _)
  simpa only [sq_abs] using
    path_risk_lower_bound hB hr (abs_nonneg (V δ - V 0)) hsep hriskEq

end NearlyMinimax
