module

public import Mathlib


@[expose] public section

/-!
# Deterministic stabilization and score-to-risk comparison

This module formalizes the clipping and denominator-stabilization step
(eq. U14-stab), the fundamental-calculus part of Lemma path-risk, and
its finite-outcome probability specialization.  The path theorem uses an
integrable derivative on the interval; it does not claim the paper's
full absolutely-continuous, almost-everywhere formulation.
-/

open scoped BigOperators
open Set MeasureTheory

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

/-- Projection of a real-valued statistic to an interval. -/
def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- Projection to the interval is `1`-Lipschitz. -/
theorem clip_lipschitz (lo hi : ℝ) : LipschitzWith 1 (clip lo hi) := by
  change LipschitzWith 1 (fun x => max lo (min hi x))
  simpa only [id_eq] using ((LipschitzWith.id.const_min hi).const_max lo)

/-- The clipped statistic lies in the designated interval. -/
theorem clip_mem_Icc {lo hi x : ℝ} (hinterval : lo ≤ hi) :
    clip lo hi x ∈ Icc lo hi := by
  exact ⟨le_max_left _ _, max_le hinterval (min_le_left _ _)⟩

/-- Any clipped statistic and interval-valued target are separated by
at most the diameter of the interval. -/
theorem clip_error_le_diameter {lo hi V x : ℝ} (hlo : lo ≤ V) (hhi : V ≤ hi) :
    |clip lo hi x - V| ≤ hi - lo := by
  have hc := clip_mem_Icc (x := x) (hlo.trans hhi)
  apply abs_le.mpr
  constructor <;> linarith [hc.1, hc.2]

/-- Clipping fixes any target in the clipping interval. -/
theorem clip_target {lo hi V : ℝ} (hlo : lo ≤ V) (hhi : V ≤ hi) :
    clip lo hi V = V := by
  simp [clip, min_eq_right hhi, max_eq_right hlo]

/-- Clipping cannot increase the absolute error at an admissible target. -/
theorem clip_error_le {lo hi V x : ℝ} (hlo : lo ≤ V) (hhi : V ≤ hi) :
    |clip lo hi x - V| ≤ |x - V| := by
  by_cases hxlo : x ≤ lo
  · have hxhi : x ≤ hi := hxlo.trans (hlo.trans hhi)
    rw [clip, min_eq_right hxhi, max_eq_left hxlo,
      abs_of_nonpos (sub_nonpos.mpr hlo), abs_of_nonpos (sub_nonpos.mpr (hxlo.trans hlo))]
    linarith
  · have hlox : lo ≤ x := le_of_lt (lt_of_not_ge hxlo)
    by_cases hxhi : x ≤ hi
    · simp [clip, min_eq_right hxhi, max_eq_right hlox]
    · have hhix : hi ≤ x := le_of_lt (lt_of_not_ge hxhi)
      rw [clip, min_eq_left hhix, max_eq_right (hlo.trans hhi),
        abs_of_nonneg (sub_nonneg.mpr hhi),
        abs_of_nonneg (sub_nonneg.mpr (hhi.trans hhix))]
      linarith

/-- A denominator floored at `a` can move only as much as its discrepancy
from a reference mean greater than `a`. -/
theorem denominator_floor_error {a D ED : ℝ} (hED : a ≤ ED) :
    |max D a - D| ≤ |D - ED| := by
  by_cases hDa : a ≤ D
  · simp [max_eq_left hDa]
  · have hDa' : D ≤ a := le_of_lt (lt_of_not_ge hDa)
    rw [max_eq_right hDa', abs_of_nonneg (sub_nonneg.mpr hDa'),
      abs_of_nonpos (sub_nonpos.mpr (hDa'.trans hED))]
    linarith

/-- The stabilized and clipped pair-ratio inequality (eq. U14-stab).
`ED` represents the expected denominator. -/
theorem stabilized_ratio_error {lo hi V N D ED a : ℝ}
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi)
    (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    |clip lo hi (N / max D a) - V| ≤
      a⁻¹ * (|N - V * D| + hi * |D - ED|) := by
  have hmax : 0 < max D a := ha.trans_le (le_max_right D a)
  have href : a ≤ ED := by linarith
  have hhineg : 0 ≤ hi := hV.trans hhi
  have hf := denominator_floor_error (D := D) href
  have hnum : |N - V * max D a| ≤ |N - V * D| + hi * |D - ED| := by
    calc
      |N - V * max D a| = |(N - V * D) - V * (max D a - D)| := by congr 1; ring
      _ ≤ |N - V * D| + |V * (max D a - D)| := abs_sub _ _
      _ = |N - V * D| + V * |max D a - D| := by rw [abs_mul, abs_of_nonneg hV]
      _ ≤ |N - V * D| + hi * |D - ED| := by
        gcongr
  have hmain : |N / max D a - V| ≤
      a⁻¹ * (|N - V * D| + hi * |D - ED|) := by
    have hid : N / max D a - V = (N - V * max D a) / max D a := by
      field_simp
    rw [hid, abs_div, abs_of_pos hmax]
    have htotal : 0 ≤ |N - V * D| + hi * |D - ED| := by positivity
    calc
      |N - V * max D a| / max D a ≤
          (|N - V * D| + hi * |D - ED|) / max D a := by
        exact div_le_div_of_nonneg_right hnum hmax.le
      _ ≤ (|N - V * D| + hi * |D - ED|) / a :=
        div_le_div_of_nonneg_left htotal ha (le_max_right D a)
      _ = _ := by ring
  exact (clip_error_le hlo hhi).trans hmain

/-- The actual analytic integration step: a derivative bounded by
`r * scoreNorm` bounds the endpoint change by the integrated score norm. -/
theorem path_mean_change_le {m m' scoreNorm : ℝ → ℝ} {δ r : ℝ}
    (hδ : 0 ≤ δ)
    (hderiv : ∀ t ∈ Icc 0 δ, HasDerivAt m (m' t) t)
    (hm' : IntervalIntegrable m' volume 0 δ)
    (hscore : IntervalIntegrable scoreNorm volume 0 δ)
    (hbound : ∀ t ∈ Icc 0 δ, |m' t| ≤ r * scoreNorm t) :
    |m δ - m 0| ≤ r * ∫ t in (0 : ℝ)..δ, scoreNorm t := by
  have hFTC : (∫ t in (0 : ℝ)..δ, m' t) = m δ - m 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa [uIcc_of_le hδ] using hderiv) hm'
  rw [← hFTC, ← intervalIntegral.integral_const_mul]
  simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le (f := m') hδ
    (Filter.Eventually.of_forall (fun t ht => by
      simpa [Real.norm_eq_abs] using hbound t ⟨le_of_lt ht.1, ht.2⟩))
    (hscore.const_mul r)

/-- Two endpoint errors and the integrated derivative bound imply the
linear score-to-risk bound of Lemma path-risk. -/
theorem path_separation_le {m m' scoreNorm : ℝ → ℝ} {δ r V₀ Vδ : ℝ}
    (hδ : 0 ≤ δ)
    (hderiv : ∀ t ∈ Icc 0 δ, HasDerivAt m (m' t) t)
    (hm' : IntervalIntegrable m' volume 0 δ)
    (hscore : IntervalIntegrable scoreNorm volume 0 δ)
    (hbound : ∀ t ∈ Icc 0 δ, |m' t| ≤ r * scoreNorm t)
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + ∫ t in (0 : ℝ)..δ, scoreNorm t) * r := by
  have hchange := path_mean_change_le hδ hderiv hm' hscore hbound
  calc
    |Vδ - V₀| = |(Vδ - m δ) + (m δ - m 0) + (m 0 - V₀)| := by congr 1; ring
    _ ≤ |Vδ - m δ| + |m δ - m 0| + |m 0 - V₀| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ r + (r * ∫ t in (0 : ℝ)..δ, scoreNorm t) + r := by
      rw [abs_sub_comm Vδ (m δ)]
      exact add_le_add (add_le_add hlast hchange) hfirst
    _ = _ := by ring

/-- Squaring the comparison and subtracting the exceptional-state
contribution yields the risk lower bound in eq. path-risk. -/
theorem path_risk_lower_bound {Δ B r risk D ε : ℝ}
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ)
    (hsep : Δ ≤ (2 + B) * r)
    (hrisk : r ^ 2 = risk + D ^ 2 * ε) :
    Δ ^ 2 / (2 + B) ^ 2 - D ^ 2 * ε ≤ risk := by
  have hden : 0 < 2 + B := by linarith
  have hsq : Δ ^ 2 ≤ ((2 + B) * r) ^ 2 := by
    have hprod : 0 ≤ (2 + B) * r := mul_nonneg hden.le hr
    exact (sq_le_sq₀ hΔ hprod).mpr hsep
  have hdiv : Δ ^ 2 / (2 + B) ^ 2 ≤ r ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith [hsq]
  linarith

/-- Weighted Cauchy–Schwarz for a finite observation space. -/
theorem finite_weighted_cauchy_schwarz_sq {α : Type*} (s : Finset α)
    (w f g : α → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) :
    (∑ x ∈ s, w x * f x * g x) ^ 2 ≤
      (∑ x ∈ s, w x * (f x) ^ 2) * ∑ x ∈ s, w x * (g x) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (fun x hx => mul_nonneg (hw x hx) (sq_nonneg (f x)))
    (fun x hx => mul_nonneg (hw x hx) (sq_nonneg (g x)))
  intro x hx
  ring

/-- `L²` risk bounds an expectation under a finite probability law. -/
theorem finite_mean_error_le {α : Type*} (s : Finset α)
    (w T : α → ℝ) (V r : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (hprob : ∑ x ∈ s, w x = 1) (hr : 0 ≤ r)
    (hrisk : (∑ x ∈ s, w x * (T x - V) ^ 2) ≤ r ^ 2) :
    |(∑ x ∈ s, w x * T x) - V| ≤ r := by
  have hcs := finite_weighted_cauchy_schwarz_sq s w (fun x => T x - V) (fun _ => 1) hw
  have hsum : (∑ x ∈ s, w x * (T x - V)) = (∑ x ∈ s, w x * T x) - V := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hprob, one_mul]
  simp only [mul_one, one_pow] at hcs
  rw [hprob, mul_one, hsum] at hcs
  have habs : |(∑ x ∈ s, w x * T x) - V| ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using hcs.trans hrisk
  exact (sq_le_sq₀ (abs_nonneg _) hr).mp habs

/-- A centered score gives the derivative bound used in Lemma path-risk,
proved by finite weighted Cauchy–Schwarz. -/
theorem finite_score_bound {α : Type*} (s : Finset α)
    (w T R : α → ℝ) (V r : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (hcenter : ∑ x ∈ s, w x * R x = 0) (hr : 0 ≤ r)
    (hrisk : (∑ x ∈ s, w x * (T x - V) ^ 2) ≤ r ^ 2) :
    |∑ x ∈ s, w x * T x * R x| ≤
      r * Real.sqrt (∑ x ∈ s, w x * (R x) ^ 2) := by
  have hcentered : (∑ x ∈ s, w x * T x * R x) =
      ∑ x ∈ s, w x * (T x - V) * R x := by
    simp_rw [mul_sub, sub_mul]
    rw [Finset.sum_sub_distrib]
    have heq : (∑ x ∈ s, w x * V * R x) = V * ∑ x ∈ s, w x * R x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [heq, hcenter, mul_zero, sub_zero]
  rw [hcentered]
  have hcs := finite_weighted_cauchy_schwarz_sq s w (fun x => T x - V) R hw
  have hsnonneg : 0 ≤ ∑ x ∈ s, w x * (R x) ^ 2 := by
    exact Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (sq_nonneg _))
  have hsq : |∑ x ∈ s, w x * (T x - V) * R x| ^ 2 ≤
      (r * Real.sqrt (∑ x ∈ s, w x * (R x) ^ 2)) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt hsnonneg]
    exact hcs.trans (mul_le_mul_of_nonneg_right hrisk hsnonneg)
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hr (Real.sqrt_nonneg _))).mp hsq

/-- A finite probability path with its actual score obeys the linear
score-to-risk comparison.  Both endpoint errors and the derivative bound
are consequences of the supplied mean-square risk bound. -/
theorem finite_score_path_separation_le {α : Type*} (s : Finset α)
    (w : ℝ → α → ℝ) (T : α → ℝ) (R : ℝ → α → ℝ) (V : ℝ → ℝ)
    (δ r : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hw : ∀ t ∈ Icc 0 δ, ∀ x ∈ s, 0 ≤ w t x)
    (hprob : ∀ t ∈ Icc 0 δ, ∑ x ∈ s, w t x = 1)
    (hcenter : ∀ t ∈ Icc 0 δ, ∑ x ∈ s, w t x * R t x = 0)
    (hderiv : ∀ t ∈ Icc 0 δ, ∀ x ∈ s,
      HasDerivAt (fun u => w u x) (w t x * R t x) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∑ x ∈ s, w t x * (T x - V t) ^ 2) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∑ x ∈ s, w t x * (R t x) ^ 2)) volume 0 δ)
    (hderivInt : IntervalIntegrable
      (fun t => ∑ x ∈ s, w t x * T x * R t x) volume 0 δ) :
    |V δ - V 0| ≤
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∑ x ∈ s, w t x * (R t x) ^ 2)) * r := by
  have hmderiv : ∀ t ∈ Icc 0 δ,
      HasDerivAt (fun u => ∑ x ∈ s, w u x * T x)
        (∑ x ∈ s, w t x * T x * R t x) t := by
    intro t ht
    simpa only [Finset.sum_fn, mul_assoc, mul_comm, mul_left_comm] using
      HasDerivAt.sum (u := s) (fun x hx => (hderiv t ht x hx).mul_const (T x))
  apply path_separation_le hδ hmderiv hderivInt hscoreInt
  · intro t ht
    exact finite_score_bound s (w t) T (R t) (V t) r (hw t ht) (hcenter t ht) hr (hrisk t ht)
  · exact finite_mean_error_le s (w 0) T (V 0) r (hw 0 ⟨le_rfl, hδ⟩)
      (hprob 0 ⟨le_rfl, hδ⟩) hr (hrisk 0 ⟨le_rfl, hδ⟩)
  · exact finite_mean_error_le s (w δ) T (V δ) r (hw δ ⟨hδ, le_rfl⟩)
      (hprob δ ⟨hδ, le_rfl⟩) hr (hrisk δ ⟨hδ, le_rfl⟩)

/-- Exceptional mixture states contribute at most the squared diameter
multiplied by their probability.  This is the finite-state counterpart
of the exceptional-state step in Lemma path-risk. -/
theorem finite_mixture_exceptional_risk_bound {α : Type*} (s : Finset α)
    (w e : α → ℝ) (bad : α → Prop) [DecidablePred bad]
    (risk D ε : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (hprob : ∑ x ∈ s, w x = 1) (hrisk : 0 ≤ risk)
    (hgood : ∀ x ∈ s, ¬ bad x → e x ≤ risk)
    (hbad : ∀ x ∈ s, bad x → e x ≤ D ^ 2)
    (hmass : (∑ x ∈ s with bad x, w x) ≤ ε) :
    (∑ x ∈ s, w x * e x) ≤ risk + D ^ 2 * ε := by
  have hpoint : ∀ x ∈ s, e x ≤ risk + if bad x then D ^ 2 else 0 := by
    intro x hx
    by_cases hb : bad x
    · simp only [if_pos hb]
      linarith [hbad x hx hb]
    · simpa only [if_neg hb, add_zero] using hgood x hx hb
  calc
    (∑ x ∈ s, w x * e x) ≤
        ∑ x ∈ s, w x * (risk + if bad x then D ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x hx) (hw x hx)
    _ = risk + D ^ 2 * ∑ x ∈ s with bad x, w x := by
      simp_rw [mul_add, mul_ite, mul_zero]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hprob, one_mul,
        ← Finset.sum_filter]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ risk + D ^ 2 * ε := by gcongr

/-- Squared lower bound for a finite score path, including the
exceptional-state correction, derived from the path theorem above. -/
theorem finite_score_path_risk_lower_bound {α : Type*} (s : Finset α)
    (w : ℝ → α → ℝ) (T : α → ℝ) (R : ℝ → α → ℝ) (V : ℝ → ℝ)
    (δ r risk D ε : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hw : ∀ t ∈ Icc 0 δ, ∀ x ∈ s, 0 ≤ w t x)
    (hprob : ∀ t ∈ Icc 0 δ, ∑ x ∈ s, w t x = 1)
    (hcenter : ∀ t ∈ Icc 0 δ, ∑ x ∈ s, w t x * R t x = 0)
    (hderiv : ∀ t ∈ Icc 0 δ, ∀ x ∈ s,
      HasDerivAt (fun u => w u x) (w t x * R t x) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∑ x ∈ s, w t x * (T x - V t) ^ 2) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∑ x ∈ s, w t x * (R t x) ^ 2)) volume 0 δ)
    (hderivInt : IntervalIntegrable
      (fun t => ∑ x ∈ s, w t x * T x * R t x) volume 0 δ)
    (hriskEq : r ^ 2 = risk + D ^ 2 * ε) :
    (V δ - V 0) ^ 2 /
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∑ x ∈ s, w t x * (R t x) ^ 2)) ^ 2
      - D ^ 2 * ε ≤ risk := by
  have hsep := finite_score_path_separation_le s w T R V δ r hδ hr hw hprob hcenter
    hderiv hrisk hscoreInt hderivInt
  have hB : 0 ≤ ∫ t in (0 : ℝ)..δ, Real.sqrt (∑ x ∈ s, w t x * (R t x) ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hδ (fun t => Real.sqrt_nonneg _)
  simpa only [sq_abs] using path_risk_lower_bound hB hr (abs_nonneg (V δ - V 0)) hsep hriskEq

/-- Integral Cauchy–Schwarz on an arbitrary measure space, stated with
ordinary real second moments. -/
theorem integral_cauchy_schwarz {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have hholder : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder
    (by simpa using hf) (by simpa using hg)
  have hcs' : (∫ x, |f x| * |g x| ∂μ) ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hcs
  calc
    |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ = ∫ x, |f x| * |g x| ∂μ := by simp_rw [abs_mul]
    _ ≤ _ := hcs'

/-- Mean-square risk controls bias for arbitrary probability laws. -/
theorem probability_mean_error_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (T : α → ℝ) (V r : ℝ)
    (hT : MemLp T 2 μ) (hr : 0 ≤ r)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |(∫ x, T x ∂μ) - V| ≤ r := by
  have hcenter : MemLp (fun x => T x - V) 2 μ := hT.sub (memLp_const V)
  have hcs := integral_cauchy_schwarz μ (fun x => T x - V) (fun _ => 1) hcenter (memLp_const 1)
  have hTInt : Integrable T μ := hT.integrable (by norm_num)
  have hVInt : Integrable (fun _ : α => V) μ := integrable_const V
  simp only [mul_one, one_pow] at hcs
  rw [integral_sub hTInt hVInt] at hcs
  simp only [integral_const, probReal_univ, one_smul, Real.sqrt_one, mul_one] at hcs
  exact hcs.trans ((Real.sqrt_le_iff).mpr ⟨hr, hrisk⟩)

/-- Centering and integral Cauchy–Schwarz prove the score derivative
bound on arbitrary probability spaces. -/
theorem probability_score_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (T R : α → ℝ) (V r : ℝ)
    (hT : MemLp T 2 μ) (hR : MemLp R 2 μ) (hr : 0 ≤ r)
    (hcenter : (∫ x, R x ∂μ) = 0)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |∫ x, T x * R x ∂μ| ≤ r * Real.sqrt (∫ x, (R x) ^ 2 ∂μ) := by
  have hTRInt : Integrable (fun x => T x * R x) μ := hT.integrable_mul hR
  have hVRInt : Integrable (fun x => V * R x) μ :=
    (hR.const_mul V).integrable (by norm_num)
  have hid : (∫ x, (T x - V) * R x ∂μ) = ∫ x, T x * R x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hTRInt hVRInt, integral_const_mul, hcenter, mul_zero, sub_zero]
  have hcs := integral_cauchy_schwarz μ (fun x => T x - V) R
    (hT.sub (memLp_const V)) hR
  rw [hid] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right
    ((Real.sqrt_le_iff).mpr ⟨hr, hrisk⟩) (Real.sqrt_nonneg _))

end NearlyMinimax
