module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic


@[expose] public section

/-!
# Rate algebra and conditional asymptotic consequences

This file formalizes the algebra of the exponents and the analytic consequences
of the rate bracket in the paper. The statistical upper and lower bounds are
explicit hypotheses of the corollaries; they are not asserted here.
-/

noncomputable section

namespace NearlyMinimax

open Filter
open scoped Topology

/-- The root-mean-square polynomial exponent. -/
def rateExponent (s d : ℝ) : ℝ := 2 * (s + 1) / (d + 4)

/-- The logarithmic power in the lower risk scale. -/
def lowerLogPower (s d : ℝ) : ℝ := (s - 1) / (d + 4)

/-- The common stretched-exponential constant in the paper. -/
def stretchConstant (s d τ : ℝ) : ℝ :=
  4 * Real.sqrt (2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3)

theorem rateExponent_pos {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) :
    0 < rateExponent s d := by
  unfold rateExponent
  have : 0 < d + 4 := by linarith
  positivity

theorem rateExponent_lt_half {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) :
    rateExponent s d < 1 / 2 := by
  unfold rateExponent
  have hp : 0 < d + 4 := by linarith
  apply (div_lt_iff₀ hp).2
  linarith

/-- Equation `eq:intro-gap`. -/
theorem conjecturedExponent_gap {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) :
    4 * s / (d + 4 * s) - rateExponent s d =
      2 * (s - 1) * (d - 4 * s) / ((d + 4 * s) * (d + 4)) := by
  have h₁ : d + 4 * s ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold rateExponent
  field_simp
  ring

theorem rateExponent_lt_conjectured {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) :
    rateExponent s d < 4 * s / (d + 4 * s) := by
  have hg := conjecturedExponent_gap hs hd
  have hp : 0 < 2 * (s - 1) * (d - 4 * s) / ((d + 4 * s) * (d + 4)) := by
    have : 0 < d + 4 * s := by linarith
    have : 0 < d + 4 := by linarith
    have : 0 < s - 1 := by linarith
    have : 0 < d - 4 * s := by linarith
    positivity
  linarith

theorem fixedDesignExponent_gap {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) :
    rateExponent s d - 2 * s / d = 2 * (d - 4 * s) / (d * (d + 4)) := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold rateExponent
  field_simp
  ring

theorem fixedDesignExponent_lt_rate {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) :
    2 * s / d < rateExponent s d := by
  have hg := fixedDesignExponent_gap hs hd
  have hp : 0 < 2 * (d - 4 * s) / (d * (d + 4)) := by
    have : 0 < d := by linarith
    have : 0 < d + 4 := by linarith
    have : 0 < d - 4 * s := by linarith
    positivity
  linarith

theorem half_minus_rateExponent {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) :
    1 / 2 - rateExponent s d = (d - 4 * s) / (2 * (d + 4)) := by
  have h : d + 4 ≠ 0 := by linarith
  unfold rateExponent
  field_simp
  ring

theorem stretchConstant_pos {s d τ : ℝ} (hs : 1 < s) (hd : 4 * s < d)
    (hτ : 0 < τ) : 0 < stretchConstant s d τ := by
  unfold stretchConstant
  have : 0 < d + 4 := by linarith
  have : 0 < s - 1 := by linarith
  have : 0 < d - 4 * s := by linarith
  positivity

/-- The upper allocation's leading square-root coefficient `a_*`. -/
def upperSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt (8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)))

/-- The lower allocation's leading coefficient `m_*`. -/
def lowerSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt (8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ))

/-- The upper saddle identifies the paper's stretched-exponential constant. -/
theorem upper_saddle_stretchConstant {s d τ : ℝ} (hs : 1 < s)
    (hd : 4 * s < d) (hτ : 0 < τ) :
    2 * (s - 1) / (d + 4) * upperSaddleCoefficient s d τ = stretchConstant s d τ := by
  have hd₀ : 0 < d := by linarith
  have hdp : 0 < d + 4 := by linarith
  have hsm : 0 < s - 1 := by linarith
  have hds : 0 < d - 4 * s := by linarith
  have hu : 0 ≤ 8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)) := by positivity
  have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
  unfold upperSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  simp only [mul_pow, div_pow, Real.sq_sqrt hu, Real.sq_sqrt hk]
  field_simp
  ring

/-- The lower saddle gives exactly the same stretched-exponential constant. -/
theorem lower_saddle_stretchConstant {s d τ : ℝ} (hs : 1 < s)
    (hd : 4 * s < d) (hτ : 0 < τ) :
    2 * d * τ / (d + 4) * lowerSaddleCoefficient s d τ = stretchConstant s d τ := by
  have hd₀ : 0 < d := by linarith
  have hdp : 0 < d + 4 := by linarith
  have hsm : 0 < s - 1 := by linarith
  have hds : 0 < d - 4 * s := by linarith
  have hm : 0 ≤ 8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ) := by positivity
  have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
  unfold lowerSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  simp only [mul_pow, div_pow, Real.sq_sqrt hm, Real.sq_sqrt hk]
  field_simp
  ring

/-- Logarithm of the unrounded bandwidth `h°` in `eq:Urate-h`. -/
def spatialBalanceLog (s d L T : ℝ) : ℝ :=
  2 / (d + 4) * (-L + 2 * ((s - 1) / d) * (L + T))

/-- Exact equality of the bias and pair-noise logarithms, before rounding. -/
theorem spatial_balance {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) (L T : ℝ) :
    2 * spatialBalanceLog s d L T - 2 * ((s - 1) / d) * (L + T) =
      -L - d / 2 * spatialBalanceLog s d L T := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold spatialBalanceLog
  field_simp
  ring

/-- The exact risk exponent identity in `eq:Urate-scale`. -/
theorem spatial_balance_rate {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d) (L T : ℝ) :
    -L - d / 2 * spatialBalanceLog s d L T =
      -rateExponent s d * L - 2 * (s - 1) / (d + 4) * T := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold spatialBalanceLog rateExponent
  field_simp
  ring

/-- Exact algebra of the lower saddle's logarithm of `N`. -/
def lowerSaddleLogN (s d L ω τ M : ℝ) : ℝ :=
  ((d - 4 * s) / d * L - (1 + 4 * s / d) * ω - 2 * τ * M) / (d + 4)

/-- The first line of `eq:LB-saddle`, excluding the constant amplitude term. -/
theorem lower_saddle_rate {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d)
    (L ω τ M : ℝ) :
    -2 * s / d * (L + ω) - 2 * lowerSaddleLogN s d L ω τ M - τ * M =
      -rateExponent s d * L - (2 * (s - 1) * ω + d * τ * M) / (d + 4) := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold lowerSaddleLogN rateExponent
  field_simp
  ring

/-- Logarithm of the general rate scale, with arbitrary log-power `a`. -/
def rateLog (lam κ a x : ℝ) : ℝ :=
  -lam * Real.log x - κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)

/-- A total real-valued definition of the scale; asymptotic results use `x > 1`. -/
def rateScale (lam κ a x : ℝ) : ℝ := Real.exp (rateLog lam κ a x)

theorem rateScale_pos (lam κ a x : ℝ) : 0 < rateScale lam κ a x := Real.exp_pos _

theorem log_rateScale (lam κ a x : ℝ) :
    Real.log (rateScale lam κ a x) = rateLog lam κ a x := Real.log_exp _

theorem rateScale_eq_base_mul_correction (lam κ a x : ℝ) :
    rateScale lam κ a x = Real.exp (-lam * Real.log x) *
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) := by
  unfold rateScale rateLog
  rw [← Real.exp_add]
  congr 1
  ring

/-- Equivalence with the paper's product using real powers. -/
theorem rateScale_eq_rpow (lam κ a : ℝ) {x : ℝ} (hx : 1 < x) :
    rateScale lam κ a x =
      x ^ (-lam) * Real.exp (-κ * Real.sqrt (Real.log x)) * (Real.log x) ^ a := by
  have hx₀ : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hl]
  unfold rateScale rateLog
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem tendsto_sqrt_div_self :
    Tendsto (fun x : ℝ => Real.sqrt x / x) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hx.ne']
  norm_num

theorem tendsto_log_div_sqrt :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero

theorem tendsto_sqrt_log_div_log :
    Tendsto (fun x : ℝ => Real.sqrt (Real.log x) / Real.log x) atTop (𝓝 0) :=
  tendsto_sqrt_div_self.comp Real.tendsto_log_atTop

theorem tendsto_loglog_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

theorem tendsto_const_div_log (c : ℝ) :
    Tendsto (fun x : ℝ => c / Real.log x) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul c)

/-- Every fixed square-root and iterated-log correction is subpolynomial. -/
theorem tendsto_correction_div_log (κ a : ℝ) :
    Tendsto (fun x : ℝ =>
      (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) / Real.log x)
      atTop (𝓝 0) := by
  have h := (tendsto_sqrt_log_div_log.const_mul (-κ)).add
    (tendsto_loglog_div_log.const_mul a)
  convert h using 1 <;> simp [add_div, mul_div_assoc, neg_div]

/-- A stretched exponential in `sqrt(log x)` defeats every fixed log-power. -/
theorem tendsto_stretched_log_factor {κ : ℝ} (hκ : 0 < κ) (a : ℝ) :
    Tendsto (fun x : ℝ =>
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp Real.tendsto_log_atTop
  have hl := tendsto_log_div_sqrt.comp Real.tendsto_log_atTop
  have hr : Tendsto (fun x : ℝ => -κ + a *
      (Real.log (Real.log x) / Real.sqrt (Real.log x))) atTop (𝓝 (-κ)) := by
    simpa using tendsto_const_nhds.add (hl.const_mul a)
  have hm := hs.atTop_mul_neg (neg_neg_of_pos hκ) hr
  apply Real.tendsto_exp_atBot.comp
  refine hm.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hp : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp

/-- A quantitative eventual form of subpolynomiality, on both sides. -/
theorem eventually_correction_between_powers (κ a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x ^ (-ε) ≤ Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ∧
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ≤ x ^ ε := by
  have h := tendsto_correction_div_log κ a
  filter_upwards [h.eventually (lt_mem_nhds (neg_lt_zero.2 hε)),
    h.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)] with x hlo hhi hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx₀ : 0 < x := by linarith
  rw [Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hx₀]
  constructor
  · apply Real.exp_le_exp.2
    have := (lt_div_iff₀ hl).1 hlo
    linarith
  · apply Real.exp_le_exp.2
    have := (div_lt_iff₀ hl).1 hhi
    linarith

theorem tendsto_normalized_log_scale (lam κ a c : ℝ) :
    Tendsto (fun x : ℝ => (-c - rateLog lam κ a x) / Real.log x) atTop (𝓝 lam) := by
  have h := (tendsto_const_nhds (x := lam)).sub
    (tendsto_correction_div_log κ a) |>.sub (tendsto_const_div_log c)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold rateLog
  field_simp
  ring

/-- The rate bracket is an explicit assumption, not a statistical theorem. -/
def HasRateBracket (risk : ℝ → ℝ) (lam κ a Γ : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ x in atTop, c * rateScale lam κ a x ≤ risk x ∧
      risk x ≤ C * rateScale lam κ (a + Γ) x

/-- Conditional version of the exponent-limit assertion in `thm:exponent`. -/
theorem exponent_limit_of_rateBracket {risk : ℝ → ℝ} {lam κ a Γ : ℝ}
    (h : HasRateBracket risk lam κ a Γ) :
    Tendsto (fun x : ℝ => -Real.log (risk x) / Real.log x) atTop (𝓝 lam) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_normalized_log_scale lam κ (a + Γ) (Real.log C))
    (tendsto_normalized_log_scale lam κ a (Real.log c))
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
    have hr : 0 < risk x := (mul_pos hc (rateScale_pos _ _ _ _)).trans_le hx.1
    have hl := Real.log_le_log hr hx.2
    rw [Real.log_mul hC.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hx₁).le
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
    have hl := Real.log_le_log (mul_pos hc (rateScale_pos _ _ _ _)) hx.1
    rw [Real.log_mul hc.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hx₁).le

/-- Conditional polynomial bounds in `thm:exponent`, retaining bracket constants. -/
theorem polynomial_bounds_of_rateBracket {risk : ℝ → ℝ} {lam κ a Γ : ℝ}
    (hκ : 0 < κ) (h : HasRateBracket risk lam κ a Γ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x in atTop, c * x ^ (-lam - ε) ≤ risk x ∧ risk x ≤ C * x ^ (-lam) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  refine ⟨c, C, hc, hC, fun ε hε => ?_⟩
  have hf := tendsto_stretched_log_factor hκ (a + Γ)
  filter_upwards [hb, eventually_correction_between_powers κ a hε,
    hf.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with x hx hl hu hx₁
  have hx₀ : 0 < x := by linarith
  have hp : 0 < Real.exp (-lam * Real.log x) := Real.exp_pos _
  constructor
  · apply le_trans _ hx.1
    rw [rateScale_eq_base_mul_correction]
    have hr : x ^ (-lam - ε) = Real.exp (-lam * Real.log x) * x ^ (-ε) := by
      rw [Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hx₀, ← Real.exp_add]
      congr 1
      ring
    rw [hr]
    simp only [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hl.1 (mul_pos hc hp).le
  · apply le_trans hx.2
    rw [rateScale_eq_base_mul_correction, Real.rpow_def_of_pos hx₀]
    have he : Real.log x * -lam = -lam * Real.log x := mul_comm _ _
    rw [he]
    calc
      C * (Real.exp (-lam * Real.log x) *
          Real.exp (-κ * Real.sqrt (Real.log x) + (a + Γ) * Real.log (Real.log x)))
          ≤ C * (Real.exp (-lam * Real.log x) * 1) := by gcongr
      _ = C * Real.exp (-lam * Real.log x) := by ring

/-- The bracket entails a strict improvement over the bare polynomial rate. -/
theorem normalized_risk_tends_zero_of_rateBracket {risk : ℝ → ℝ} {lam κ a Γ : ℝ}
    (hκ : 0 < κ) (h : HasRateBracket risk lam κ a Γ) :
    Tendsto (fun x : ℝ => x ^ lam * risk x) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply squeeze_zero' (g := fun x : ℝ => C *
    Real.exp (-κ * Real.sqrt (Real.log x) + (a + Γ) * Real.log (Real.log x)))
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
    have hr : 0 < risk x := (mul_pos hc (rateScale_pos _ _ _ _)).trans_le hx.1
    positivity
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
    have hx₀ : 0 < x := by linarith
    have hr := mul_le_mul_of_nonneg_left hx.2 (Real.rpow_pos_of_pos hx₀ lam).le
    rw [rateScale_eq_base_mul_correction, Real.rpow_def_of_pos hx₀] at hr
    have he : Real.exp (Real.log x * lam) * Real.exp (-lam * Real.log x) = 1 := by
      rw [← Real.exp_add]
      have hz : Real.log x * lam + -lam * Real.log x = 0 := by ring
      rw [hz, Real.exp_zero]
    rw [Real.rpow_def_of_pos hx₀]
    calc
      Real.exp (Real.log x * lam) * risk x ≤
          Real.exp (Real.log x * lam) * (C * (Real.exp (-lam * Real.log x) *
            Real.exp (-κ * Real.sqrt (Real.log x) + (a + Γ) * Real.log (Real.log x)))) := hr
      _ = C * (Real.exp (Real.log x * lam) * Real.exp (-lam * Real.log x)) *
          Real.exp (-κ * Real.sqrt (Real.log x) + (a + Γ) * Real.log (Real.log x)) := by ring
      _ = C * Real.exp (-κ * Real.sqrt (Real.log x) + (a + Γ) * Real.log (Real.log x)) := by rw [he]; ring
  · simpa using (tendsto_stretched_log_factor hκ (a + Γ)).const_mul C

/-- The paper indexes risk by integer sample size. The bracket remains a hypothesis. -/
def HasNatRateBracket (risk : ℕ → ℝ) (lam κ a Γ : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop, c * rateScale lam κ a (n : ℝ) ≤ risk n ∧
      risk n ≤ C * rateScale lam κ (a + Γ) (n : ℝ)

/-- Conditional natural-sample-size version of the exponent limit. -/
theorem exponent_limit_nat_of_rateBracket {risk : ℕ → ℝ} {lam κ a Γ : ℝ}
    (h : HasNatRateBracket risk lam κ a Γ) :
    Tendsto (fun n : ℕ => -Real.log (risk n) / Real.log (n : ℝ)) atTop (𝓝 lam) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((tendsto_normalized_log_scale lam κ (a + Γ) (Real.log C)).comp tendsto_natCast_atTop_atTop)
    ((tendsto_normalized_log_scale lam κ a (Real.log c)).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hr : 0 < risk n := (mul_pos hc (rateScale_pos _ _ _ _)).trans_le hn.1
    have hl := Real.log_le_log hr hn.2
    rw [Real.log_mul hC.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hl := Real.log_le_log (mul_pos hc (rateScale_pos _ _ _ _)) hn.1
    rw [Real.log_mul hc.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le

/-- Normalizing by the square-root log scale identifies the constant `κ`. -/
theorem tendsto_normalized_stretch_scale (lam κ a c : ℝ) :
    Tendsto (fun x : ℝ =>
      (c + rateLog lam κ a x + lam * Real.log x) / Real.sqrt (Real.log x))
      atTop (𝓝 (-κ)) := by
  have hc : Tendsto (fun x : ℝ => c / Real.sqrt (Real.log x)) atTop (𝓝 0) := by
    have hs : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop := by
      simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
        (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp Real.tendsto_log_atTop
    simpa [div_eq_mul_inv] using hs.inv_tendsto_atTop.const_mul c
  have hl := tendsto_log_div_sqrt.comp Real.tendsto_log_atTop
  have hh := (tendsto_const_nhds (x := -κ)).add (hl.const_mul a) |>.add hc
  simp only [mul_zero, add_zero, Function.comp_apply] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hp : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  unfold rateLog
  field_simp
  ring

/-- A second conditional consequence of the bracket: its common constant is `κ`. -/
theorem stretch_constant_limit_nat_of_rateBracket {risk : ℕ → ℝ} {lam κ a Γ : ℝ}
    (h : HasNatRateBracket risk lam κ a Γ) :
    Tendsto (fun n : ℕ =>
      (Real.log (risk n) + lam * Real.log (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)))
      atTop (𝓝 (-κ)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((tendsto_normalized_stretch_scale lam κ a (Real.log c)).comp tendsto_natCast_atTop_atTop)
    ((tendsto_normalized_stretch_scale lam κ (a + Γ) (Real.log C)).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hl := Real.log_le_log (mul_pos hc (rateScale_pos _ _ _ _)) hn.1
    rw [Real.log_mul hc.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hr : 0 < risk n := (mul_pos hc (rateScale_pos _ _ _ _)).trans_le hn.1
    have hl := Real.log_le_log hr hn.2
    rw [Real.log_mul hC.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- The claimed logarithmic expansion, with an explicit eventual error bound.
As throughout this file, obtaining the statistical bracket is a separate obligation. -/
theorem log_expansion_nat_of_rateBracket {risk : ℕ → ℝ} {lam κ a Γ : ℝ}
    (h : HasNatRateBracket risk lam κ a Γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |Real.log (risk n) + lam * Real.log (n : ℝ) + κ * Real.sqrt (Real.log (n : ℝ))|
        ≤ K * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  let K := |Real.log c| + |Real.log C| + |a| + |a + Γ| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hb, hll.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hnll
  have hl := Real.log_le_log (mul_pos hc (rateScale_pos _ _ _ _)) hn.1
  have hr : 0 < risk n := (mul_pos hc (rateScale_pos _ _ _ _)).trans_le hn.1
  have hu := Real.log_le_log hr hn.2
  rw [Real.log_mul hc.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
  rw [Real.log_mul hC.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hu
  unfold rateLog at hl hu
  have hz : 0 ≤ Real.log (Real.log (n : ℝ)) := by linarith
  have hlow := mul_le_mul_of_nonneg_right (neg_abs_le a) hz
  have hupp := mul_le_mul_of_nonneg_right (le_abs_self (a + Γ)) hz
  have hclow := neg_abs_le (Real.log c)
  have hCupp := le_abs_self (Real.log C)
  have hcabs : |Real.log c| ≤ |Real.log c| * Real.log (Real.log (n : ℝ)) :=
    le_mul_of_one_le_right (abs_nonneg _) hnll
  have hCabs : |Real.log C| ≤ |Real.log C| * Real.log (Real.log (n : ℝ)) :=
    le_mul_of_one_le_right (abs_nonneg _) hnll
  have hKl : |Real.log c| + |a| ≤ K := by
    dsimp [K]
    linarith [abs_nonneg (Real.log C), abs_nonneg (a + Γ)]
  have hKu : |Real.log C| + |a + Γ| ≤ K := by
    dsimp [K]
    linarith [abs_nonneg (Real.log c), abs_nonneg a]
  have hKlm := mul_le_mul_of_nonneg_right hKl hz
  have hKum := mul_le_mul_of_nonneg_right hKu hz
  apply abs_le.2
  constructor <;> nlinarith

end NearlyMinimax
