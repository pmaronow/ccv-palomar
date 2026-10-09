module

public import NearlyMinimax.Rates
public import NearlyMinimax.SaddleAsymptotics
public import NearlyMinimax.LowerEndpoint
public import Mathlib.Analysis.SpecialFunctions.Stirling


@[expose] public section

/-!
# The actual lower saddle allocation

This file constructs and analyzes the scalar parameters of `lem:saddle` in
`sections/lower_fisher.tex`. Natural ceilings are used for the polynomial
degree and the spatial grid. The statements in this file are deterministic
numeric allocation results; they do not postulate the local score construction
or its statistical energy estimate.
-/

noncomputable section
open Filter
open scoped Topology

namespace NearlyMinimax

def lowerSaddleM (m x : ℝ) : ℕ := Nat.ceil (m * Real.sqrt (Real.log x))

def lowerSaddleD (d m x : ℝ) : ℕ := Nat.ceil ((d + 8) / 4 * lowerSaddleM m x)

def lowerSaddleOmegaZero (m θ C x : ℝ) : ℝ :=
  θ * lowerSaddleM m x - Real.log (lowerSaddleM m x) + C

def lowerSaddleGridBase (d m θ C x : ℝ) : ℝ :=
  Real.exp ((Real.log x + lowerSaddleOmegaZero m θ C x) / d)

def lowerSaddleGrid (d m θ C x : ℝ) : ℕ := Nat.ceil (lowerSaddleGridBase d m θ C x)

def lowerSaddleH (d m θ C x : ℝ) : ℝ := (lowerSaddleGrid d m θ C x : ℝ)⁻¹

def lowerSaddleMu (d m θ C x : ℝ) : ℝ := x * (lowerSaddleH d m θ C x) ^ d

def lowerSaddleOmega (d m θ C x : ℝ) : ℝ :=
  d * Real.log (lowerSaddleGrid d m θ C x) - Real.log x

theorem lowerSaddleM_rounding {m x : ℝ} (hm : 0 ≤ m) :
    m * Real.sqrt (Real.log x) ≤ (lowerSaddleM m x : ℝ) ∧
      (lowerSaddleM m x : ℝ) < m * Real.sqrt (Real.log x) + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg hm (Real.sqrt_nonneg _))⟩

theorem lowerSaddleM_tendsto_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun x => (lowerSaddleM_rounding hm.le).1)
  exact tendsto_sqrt_log_atTop.const_mul_atTop hm

theorem lowerSaddleM_div_sqrt_log_limit {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) / Real.sqrt (Real.log x))
      atTop (𝓝 m) := by
  have herr : Tendsto (fun x : ℝ =>
      ((lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x)) /
        Real.sqrt (Real.log x)) atTop (𝓝 0) := by
    have hu : Tendsto (fun x : ℝ => 1 / Real.sqrt (Real.log x)) atTop (𝓝 0) := by
      simpa only [one_div] using! tendsto_sqrt_log_atTop.inv_tendsto_atTop
    apply squeeze_zero' _ _ hu
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_nonneg (sub_nonneg.2 (lowerSaddleM_rounding hm.le).1) (Real.sqrt_nonneg _)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_le_div_of_nonneg_right (by linarith [(lowerSaddleM_rounding (x := x) hm.le).2])
        (Real.sqrt_nonneg _)
  have hh := (tendsto_const_nhds (x := m)).add herr
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hz : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp
  ring

theorem lowerSaddleM_sq_div_log_limit {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) ^ 2 / Real.log x) atTop (𝓝 (m ^ 2)) := by
  have hh := (lowerSaddleM_div_sqrt_log_limit hm).pow 2
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [div_pow, Real.sq_sqrt (Real.log_pos hx).le]

theorem log_lowerSaddleM_residual_limit {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleM m x) - Real.log (Real.log x) / 2)
      atTop (𝓝 (Real.log m)) := by
  have hh := (Real.continuousAt_log hm.ne').tendsto.comp (lowerSaddleM_div_sqrt_log_limit hm)
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx hM
  simp only [Function.comp_apply]
  rw [Real.log_div hM.ne' (Real.sqrt_pos.2 (Real.log_pos hx)).ne',
    Real.log_sqrt (Real.log_pos hx).le]

theorem lowerSaddleOmegaZero_div_M_limit {m : ℝ} (hm : 0 < m) (θ C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmegaZero m θ C x / lowerSaddleM m x)
      atTop (𝓝 θ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht
  have hc : Tendsto (fun x : ℝ => C / lowerSaddleM m x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ht.inv_tendsto_atTop.const_mul C
  have hh := ((tendsto_const_nhds (x := θ)).sub hl).add hc
  simp only [sub_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  simp only [Function.comp_apply, id_eq]
  unfold lowerSaddleOmegaZero
  field_simp

theorem lowerSaddleOmegaZero_tendsto_atTop {m θ : ℝ} (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleOmegaZero m θ C) atTop atTop := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hh := ht.atTop_mul_pos hθ (lowerSaddleOmegaZero_div_M_limit hm θ C)
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  exact mul_div_cancel₀ _ hx.ne'

theorem lowerSaddleGrid_positive (d m θ C x : ℝ) : 0 < (lowerSaddleGrid d m θ C x : ℝ) := by
  have hh := Nat.le_ceil (lowerSaddleGridBase d m θ C x)
  exact (Real.exp_pos _).trans_le hh

theorem lowerSaddleH_positive (d m θ C x : ℝ) : 0 < lowerSaddleH d m θ C x :=
  inv_pos.2 (lowerSaddleGrid_positive d m θ C x)

theorem lowerSaddleGridBase_tendsto_atTop {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleGridBase d m θ C) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.atTop_add_atTop (lowerSaddleOmegaZero_tendsto_atTop hm hθ C)).atTop_div_const hd)

theorem lowerSaddleGrid_tendsto_atTop {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => (lowerSaddleGrid d m θ C x : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun x => Nat.le_ceil _)
  exact lowerSaddleGridBase_tendsto_atTop hd hm hθ C

theorem lowerSaddleGrid_div_base_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => (lowerSaddleGrid d m θ C x : ℝ) / lowerSaddleGridBase d m θ C x)
      atTop (𝓝 1) := by
  have hb := lowerSaddleGridBase_tendsto_atTop hd hm hθ C
  have herr : Tendsto (fun x : ℝ =>
      ((lowerSaddleGrid d m θ C x : ℝ) - lowerSaddleGridBase d m θ C x) /
        lowerSaddleGridBase d m θ C x) atTop (𝓝 0) := by
    have hu : Tendsto (fun x : ℝ => 1 / lowerSaddleGridBase d m θ C x) atTop (𝓝 0) := by
      simpa only [one_div] using! hb.inv_tendsto_atTop
    apply squeeze_zero' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) hu
    · exact div_nonneg (sub_nonneg.2 (Nat.le_ceil _)) (Real.exp_pos _).le
    · apply div_le_div_of_nonneg_right _ (show 0 ≤ lowerSaddleGridBase d m θ C x from (Real.exp_pos _).le)
      change (lowerSaddleGrid d m θ C x : ℝ) - lowerSaddleGridBase d m θ C x ≤ 1
      have hh := Nat.ceil_lt_add_one (show 0 ≤ lowerSaddleGridBase d m θ C x from (Real.exp_pos _).le)
      change (lowerSaddleGrid d m θ C x : ℝ) < lowerSaddleGridBase d m θ C x + 1 at hh
      linarith
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add herr
  simp only [add_zero] at hh
  refine hh.congr (fun x => ?_)
  have hp : lowerSaddleGridBase d m θ C x ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

theorem lowerSaddleOmega_rounding_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x)
      atTop (𝓝 0) := by
  have hh := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (lowerSaddleGrid_div_base_limit hd hm hθ C)).const_mul d
  simp only [Real.log_one, mul_zero] at hh
  refine hh.congr (fun x => ?_)
  simp only [Function.comp_apply]
  rw [Real.log_div (lowerSaddleGrid_positive d m θ C x).ne'
    (show lowerSaddleGridBase d m θ C x ≠ 0 from (Real.exp_pos _).ne')]
  unfold lowerSaddleGridBase lowerSaddleOmega
  rw [Real.log_exp]
  field_simp
  ring

theorem lowerSaddleOmega_rounding_bounds {d m θ C x : ℝ} (hd : 0 < d)
    (hb : 1 ≤ lowerSaddleGridBase d m θ C x) :
    lowerSaddleOmegaZero m θ C x ≤ lowerSaddleOmega d m θ C x ∧
      lowerSaddleOmega d m θ C x ≤ lowerSaddleOmegaZero m θ C x + d * Real.log 2 := by
  have hpos : 0 < lowerSaddleGridBase d m θ C x := Real.exp_pos _
  have hlow := Real.log_le_log hpos (Nat.le_ceil (lowerSaddleGridBase d m θ C x))
  change Real.log (lowerSaddleGridBase d m θ C x) ≤
    Real.log (lowerSaddleGrid d m θ C x) at hlow
  have hceil : (lowerSaddleGrid d m θ C x : ℝ) ≤ 2 * lowerSaddleGridBase d m θ C x := by
    have hh := Nat.ceil_lt_add_one hpos.le
    change (lowerSaddleGrid d m θ C x : ℝ) < lowerSaddleGridBase d m θ C x + 1 at hh
    linarith
  have hhigh := Real.log_le_log (lowerSaddleGrid_positive d m θ C x) hceil
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpos.ne'] at hhigh
  unfold lowerSaddleGridBase at hlow hhigh
  rw [Real.log_exp] at hlow hhigh
  unfold lowerSaddleOmega
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlow hd.le,
    mul_le_mul_of_nonneg_left hhigh hd.le, mul_div_cancel₀
      (Real.log x + lowerSaddleOmegaZero m θ C x) hd.ne']

theorem lowerSaddleOmega_eq_log_inv_mu {d m θ C x : ℝ} (hx : 0 < x) :
    lowerSaddleOmega d m θ C x = Real.log (1 / lowerSaddleMu d m θ C x) := by
  unfold lowerSaddleMu
  rw [Real.log_div one_ne_zero (mul_pos hx
    (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)).ne', Real.log_one,
    Real.log_mul hx.ne' (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d).ne',
    Real.log_rpow (lowerSaddleH_positive d m θ C x)]
  unfold lowerSaddleH lowerSaddleOmega
  rw [Real.log_inv]
  ring

theorem lowerSaddleMu_eq_exp {d m θ C x : ℝ} (hx : 0 < x) :
    lowerSaddleMu d m θ C x = Real.exp (-lowerSaddleOmega d m θ C x) := by
  unfold lowerSaddleMu
  calc
    _ = Real.exp (Real.log x) * Real.exp (Real.log (lowerSaddleH d m θ C x) * d) := by
      rw [Real.exp_log hx, Real.rpow_def_of_pos (lowerSaddleH_positive d m θ C x)]
    _ = Real.exp (Real.log x + Real.log (lowerSaddleH d m θ C x) * d) := (Real.exp_add _ _).symm
    _ = _ := by
      congr 1
      unfold lowerSaddleH lowerSaddleOmega
      rw [Real.log_inv]
      ring

theorem lowerSaddleH_eq_exp {d m θ C x : ℝ} (hd : d ≠ 0) :
    lowerSaddleH d m θ C x =
      Real.exp (-(Real.log x + lowerSaddleOmega d m θ C x) / d) := by
  unfold lowerSaddleH lowerSaddleOmega
  have hh : -(Real.log x + (d * Real.log (lowerSaddleGrid d m θ C x) - Real.log x)) / d =
      -Real.log (lowerSaddleGrid d m θ C x) := by field_simp; ring
  rw [hh, Real.exp_neg, Real.exp_log (lowerSaddleGrid_positive d m θ C x)]

theorem lowerSaddleOmega_div_M_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x / lowerSaddleM m x) atTop (𝓝 θ) := by
  have hr := (lowerSaddleOmega_rounding_limit hd hm hθ C).mul
    (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  have hh := (lowerSaddleOmegaZero_div_M_limit hm θ C).add hr
  simp only [mul_zero, add_zero] at hh
  convert! hh using 1
  funext x
  change lowerSaddleOmega d m θ C x / (lowerSaddleM m x : ℝ) =
    lowerSaddleOmegaZero m θ C x / (lowerSaddleM m x : ℝ) +
    (lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x) / (lowerSaddleM m x : ℝ)
  simp only [div_eq_mul_inv]
  ring

theorem lowerSaddleOmega_tendsto_atTop {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleOmega d m θ C) atTop atTop := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hh := ht.atTop_mul_pos hθ (lowerSaddleOmega_div_M_limit hd hm hθ C)
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  exact mul_div_cancel₀ _ hx.ne'

theorem lowerSaddleM_div_log_limit {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) / Real.log x) atTop (𝓝 0) := by
  have hh := (lowerSaddleM_div_sqrt_log_limit hm).mul tendsto_sqrt_log_div_log
  simp only [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hz : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp

theorem lowerSaddleOmega_div_log_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x / Real.log x) atTop (𝓝 0) := by
  have hh := (lowerSaddleOmega_div_M_limit hd hm hθ C).mul (lowerSaddleM_div_log_limit hm)
  simp only [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  field_simp

/-- `τM` denotes the interval exponent evaluated at the actual natural degree. -/
def lowerSaddleN (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (lowerSaddleLogN s d (Real.log x) (lowerSaddleOmega d m θ C x)
    (τM (lowerSaddleM m x)) (lowerSaddleM m x))

def lowerSaddleEta (s d m θ C cf x : ℝ) : ℝ := cf * (lowerSaddleH d m θ C x) ^ s

def lowerSaddleActivity (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleN s d m θ C τM x) ^ 2 * Real.exp (τM (lowerSaddleM m x) * lowerSaddleM m x)

def lowerSaddleRisk (s d m θ C cf : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ 2 / lowerSaddleActivity s d m θ C τM x

def lowerSaddleEnergyOne (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x ^ (2 : ℕ) * (lowerSaddleH d m θ C x) ^ (d + 4 * s) *
    (lowerSaddleN s d m θ C τM x) ^ (-d)

def lowerSaddleEnergyTwo (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x * (lowerSaddleH d m θ C x) ^ (4 * s) *
    Real.exp (2 * τM (lowerSaddleM m x) * lowerSaddleM m x) *
    (lowerSaddleN s d m θ C τM x) ^ (4 - d) *
    (CG * lowerSaddleMu d m θ C x) ^ lowerSaddleM m x /
      ((lowerSaddleM m x + 1).factorial : ℝ)

def lowerSaddleEnergyThree (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x * (lowerSaddleH d m θ C x) ^ (4 * s) *
    (lowerSaddleActivity s d m θ C τM x) ^ 2 *
    (CG * lowerSaddleMu d m θ C x) ^ lowerSaddleD d m x /
      ((lowerSaddleD d m x + 1).factorial : ℝ)

theorem lowerSaddleN_positive (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) :
    0 < lowerSaddleN s d m θ C τM x := Real.exp_pos _

theorem lowerSaddleActivity_positive (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) :
    0 < lowerSaddleActivity s d m θ C τM x := by
  unfold lowerSaddleActivity
  exact mul_pos (sq_pos_of_pos (lowerSaddleN_positive s d m θ C τM x)) (Real.exp_pos _)

theorem lowerSaddleN_eq_balance {s d m θ C x : ℝ} (hd : 0 < d) (hd4 : d + 4 ≠ 0)
    (hx : 0 < x) (τM : ℕ → ℝ) :
    lowerSaddleN s d m θ C τM x =
      (x ^ (2 : ℕ) * (lowerSaddleH d m θ C x) ^ (d + 4 * s) *
        Real.exp (-2 * τM (lowerSaddleM m x) * lowerSaddleM m x)) ^ (1 / (d + 4)) := by
  have hH := lowerSaddleH_positive d m θ C x
  unfold lowerSaddleN lowerSaddleLogN
  rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (pow_ne_zero 2 hx.ne') (Real.rpow_pos_of_pos hH (d + 4 * s)).ne',
    Real.log_pow, Real.log_rpow hH, Real.log_exp,
    lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  congr 1
  field_simp
  ring

theorem lowerSaddleEnergyOne_eq_activity_sq {s d m θ C x : ℝ}
    (hd : 0 < d) (hd4 : d + 4 ≠ 0) (hx : 0 < x) (τM : ℕ → ℝ) :
    lowerSaddleEnergyOne s d m θ C τM x = (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
  have hx2 : x ^ (2 : ℕ) = Real.exp ((2 : ℝ) * Real.log x) := by
    change x ^ (2 : ℕ) = Real.exp (((2 : ℕ) : ℝ) * Real.log x)
    rw [Real.exp_nat_mul, Real.exp_log hx]
  unfold lowerSaddleEnergyOne lowerSaddleActivity lowerSaddleN
  rw [hx2, Real.rpow_def_of_pos (lowerSaddleH_positive d m θ C x),
    Real.rpow_def_of_pos (Real.exp_pos _), mul_pow]
  simp only [Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_add]
  rw [lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  congr 1
  unfold lowerSaddleLogN
  field_simp
  ring

/-- The fixed endpoint estimate `τ≤τ_M≤τ+Cτ/M`, expressed without division. -/
def LowerExponentControl (τM : ℕ → ℝ) (τ Cτ : ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop, τ ≤ τM M ∧ (τM M - τ) * (M : ℝ) ≤ Cτ

theorem lowerSaddleM_nat_tendsto_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (lowerSaddleM m) atTop atTop :=
  tendsto_natCast_atTop_iff.1 (lowerSaddleM_tendsto_atTop hm)

theorem lowerSaddleTau_limit {m τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hm : 0 < m) (hcontrol : LowerExponentControl τM τ Cτ) :
    Tendsto (fun x : ℝ => τM (lowerSaddleM m x)) atTop (𝓝 τ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have he := (lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol
  have hu : Tendsto (fun x : ℝ => Cτ / lowerSaddleM m x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using! ht.inv_tendsto_atTop.const_mul Cτ
  have hh : Tendsto (fun x : ℝ => τM (lowerSaddleM m x) - τ) atTop (𝓝 0) := by
    apply squeeze_zero' (he.mono fun x hx => sub_nonneg.2 hx.1) _ hu
    filter_upwards [he, ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hM
    exact (le_div_iff₀ hM).2 hx.2
  have h := hh.add_const τ
  simp only [zero_add, sub_add_cancel] at h
  exact h

theorem lowerSaddleLogN_div_log_limit {d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ) :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x) / Real.log x)
      atTop (𝓝 ((d - 4 * s) / (d * (d + 4)))) := by
  have hcost := (lowerSaddleTau_limit hm hcontrol).mul (lowerSaddleM_div_log_limit hm)
  have homega := (lowerSaddleOmega_div_log_limit hd hm hθ C).const_mul (1 + 4 * s / d)
  have hh := (((tendsto_const_nhds (x := (d - 4 * s) / d)).sub homega).sub
    (hcost.const_mul 2)).div_const (d + 4)
  simp only [mul_zero, sub_zero] at hh
  have hid : (d - 4 * s) / d / (d + 4) = (d - 4 * s) / (d * (d + 4)) := div_div _ _ _
  rw [hid] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  unfold lowerSaddleN lowerSaddleLogN
  rw [Real.log_exp]
  field_simp [(Real.log_pos hx).ne']

theorem lowerSaddleLogN_div_M_sq_limit {d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ) :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x) / (lowerSaddleM m x : ℝ) ^ 2)
      atTop (𝓝 (((d - 4 * s) / (d * (d + 4))) / m ^ 2)) := by
  have hh := (lowerSaddleLogN_div_log_limit hd hm hθ hcontrol s C).div
    (lowerSaddleM_sq_div_log_limit hm) (pow_ne_zero 2 hm.ne')
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  change (Real.log (lowerSaddleN s d m θ C τM x) / Real.log x) /
    ((lowerSaddleM m x : ℝ) ^ 2 / Real.log x) =
      Real.log (lowerSaddleN s d m θ C τM x) / (lowerSaddleM m x : ℝ) ^ 2
  field_simp [(Real.log_pos hx).ne']

theorem lowerSaddleN_tendsto_atTop {s d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C : ℝ) :
    Tendsto (lowerSaddleN s d m θ C τM) atTop atTop := by
  have hd0 : 0 < d := by linarith
  have hγ : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
  have hh := Real.tendsto_log_atTop.atTop_mul_pos hγ
    (lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C)
  have ht : Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x)) atTop atTop := by
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_div_cancel₀ _ (Real.log_pos hx).ne'
  have h := Real.tendsto_exp_atTop.comp ht
  exact h.congr (fun x => Real.exp_log (lowerSaddleN_positive s d m θ C τM x))

theorem lowerSaddleMu_tends_zero {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleMu d m θ C) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (lowerSaddleOmega_tendsto_atTop hd hm hθ C))
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (lowerSaddleMu_eq_exp hx).symm

theorem lowerSaddleH_tends_zero {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleH d m θ C) atTop (𝓝 0) := by
  exact (lowerSaddleGrid_tendsto_atTop hd hm hθ C).inv_tendsto_atTop

theorem lowerSaddleEta_tends_zero {s d m θ : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C cf : ℝ) :
    Tendsto (lowerSaddleEta s d m θ C cf) atTop (𝓝 0) := by
  have hh := ((lowerSaddleH_tends_zero hd hm hθ C).rpow_const (Or.inr hs.le)).const_mul cf
  simpa only [Real.zero_rpow hs.ne', mul_zero] using! hh

theorem tendsto_atBot_of_div_negative {f g : ℝ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop atTop) (hf : Tendsto (fun x => f x / g x) atTop (𝓝 c))
    (hc : c < 0) : Tendsto f atTop atBot := by
  have hh := hg.atTop_mul_neg hc hf
  refine hh.congr' ?_
  filter_upwards [hg.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  exact mul_div_cancel₀ _ hx.ne'

theorem lowerSaddleM_mul_mu_tends_zero {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) * lowerSaddleMu d m θ C x) atTop (𝓝 0) := by
  have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (lowerSaddleM_tendsto_atTop hm)).sub (lowerSaddleOmega_div_M_limit hd hm hθ C)
  simp only [zero_sub] at hh
  have ht : Tendsto (fun x : ℝ => Real.log (lowerSaddleM m x) - lowerSaddleOmega d m θ C x)
      atTop atBot := by
    apply tendsto_atBot_of_div_negative (lowerSaddleM_tendsto_atTop hm) _ (neg_neg_of_pos hθ)
    convert! hh using 1
    funext x
    change (Real.log (lowerSaddleM m x) - lowerSaddleOmega d m θ C x) / (lowerSaddleM m x : ℝ) =
      Real.log (lowerSaddleM m x) / (lowerSaddleM m x : ℝ) -
        lowerSaddleOmega d m θ C x / (lowerSaddleM m x : ℝ)
    ring
  have h := Real.tendsto_exp_atBot.comp ht
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx hM
  simp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_log hM, lowerSaddleMu_eq_exp hx, Real.exp_neg]
  rfl

theorem lowerSaddleRisk_positive {s d m θ C cf x : ℝ} (hcf : 0 < cf) (τM : ℕ → ℝ) :
    0 < lowerSaddleRisk s d m θ C cf τM x := by
  unfold lowerSaddleRisk lowerSaddleEta
  exact div_pos (sq_pos_of_pos (mul_pos hcf
    (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)))
    (lowerSaddleActivity_positive s d m θ C τM x)

theorem log_lowerSaddleRisk {s d m θ C cf x : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hcf : 0 < cf) (τM : ℕ → ℝ) :
    Real.log (lowerSaddleRisk s d m θ C cf τM x) =
      2 * Real.log cf - rateExponent s d * Real.log x -
        (2 * (s - 1) * lowerSaddleOmega d m θ C x +
          d * τM (lowerSaddleM m x) * lowerSaddleM m x) / (d + 4) := by
  have hd0 : 0 < d := by linarith
  have hH := lowerSaddleH_positive d m θ C x
  have hN := lowerSaddleN_positive s d m θ C τM x
  have hEta : 0 < lowerSaddleEta s d m θ C cf x :=
    mul_pos hcf (Real.rpow_pos_of_pos hH s)
  unfold lowerSaddleRisk
  rw [Real.log_div (pow_ne_zero 2 hEta.ne') (lowerSaddleActivity_positive s d m θ C τM x).ne',
    Real.log_pow]
  unfold lowerSaddleEta lowerSaddleActivity
  rw [Real.log_mul hcf.ne' (Real.rpow_pos_of_pos hH s).ne', Real.log_rpow hH,
    Real.log_mul (pow_ne_zero 2 hN.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp,
    lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
  unfold lowerSaddleN
  rw [Real.log_exp]
  have hh := lower_saddle_rate hs hd (Real.log x) (lowerSaddleOmega d m θ C x)
    (τM (lowerSaddleM m x)) (lowerSaddleM m x)
  ring_nf at hh ⊢
  linarith

theorem log_factorial_succ_lower (M : ℕ) (hM : 1 ≤ M) :
    (M : ℝ) * Real.log M - M ≤ Real.log ((M + 1).factorial : ℝ) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hs := Stirling.le_log_factorial_stirling (Nat.ne_of_gt (by omega : 0 < M))
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hfac : (M.factorial : ℝ) ≤ ((M + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ M)
  have hl := Real.log_le_log (by positivity : 0 < (M.factorial : ℝ)) hfac
  linarith

theorem log_lowerSaddleEnergyTwo_ratio {s d m θ C CG x : ℝ}
    (hd : 0 < d) (hCG : 0 < CG) (hx : 0 < x) (τM : ℕ → ℝ) :
    Real.log (lowerSaddleEnergyTwo s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) =
    4 * ((d - 4 * s) / (d * (d + 4))) * Real.log x +
      ((d ^ 2 - 16 * s) / (d * (d + 4)) - lowerSaddleM m x) * lowerSaddleOmega d m θ C x +
      (2 * d * τM (lowerSaddleM m x) / (d + 4) + Real.log CG) * lowerSaddleM m x -
      Real.log ((lowerSaddleM m x + 1).factorial : ℝ) := by
  have hMu : 0 < lowerSaddleMu d m θ C x := by
    unfold lowerSaddleMu
    exact mul_pos hx (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
  have hH := lowerSaddleH_positive d m θ C x
  have hN := lowerSaddleN_positive s d m θ C τM x
  have hA := lowerSaddleActivity_positive s d m θ C τM x
  have hfac : 0 < ((lowerSaddleM m x + 1).factorial : ℝ) := by positivity
  unfold lowerSaddleEnergyTwo
  rw [Real.log_div (by positivity) (pow_ne_zero 2 hA.ne'),
    Real.log_div (by positivity) hfac.ne', Real.log_pow]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow hH, Real.log_exp, Real.log_rpow hN, Real.log_pow,
    Real.log_mul hCG.ne' hMu.ne', lowerSaddleMu_eq_exp hx, Real.log_exp]
  unfold lowerSaddleActivity lowerSaddleN
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp, Real.log_exp,
    lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  unfold lowerSaddleLogN
  field_simp
  ring

theorem lowerSaddleM_square_balance {m θ γ x : ℝ}
    (hm : 0 < m) (hθ : 0 < θ) (hbalance : θ * m ^ 2 = 4 * γ)
    (hx : 1 ≤ x) : 4 * γ * Real.log x ≤ θ * (lowerSaddleM m x : ℝ) ^ 2 := by
  have hr := (lowerSaddleM_rounding (x := x) hm.le).1
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ m * Real.sqrt (Real.log x)) (by positivity)).2 hr
  rw [mul_pow, Real.sq_sqrt (Real.log_nonneg hx)] at hsq
  have hh := mul_le_mul_of_nonneg_left hsq hθ.le
  rw [← mul_assoc, hbalance] at hh
  exact hh

def lowerSaddleAliasUpper (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (d ^ 2 - 16 * s) / (d * (d + 4)) * lowerSaddleOmega d m θ C x +
    (2 * d * τM (lowerSaddleM m x) / (d + 4) + Real.log CG + 1 - C) * lowerSaddleM m x

theorem eventually_log_energyTwo_le_aliasUpper {s d m θ C CG : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG)
    (hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4)))) :
    ∀ᶠ x : ℝ in atTop,
      Real.log (lowerSaddleEnergyTwo s d m θ C CG τM x /
        (lowerSaddleActivity s d m θ C τM x) ^ 2) ≤ lowerSaddleAliasUpper s d m θ C CG τM x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop (1 : ℝ)),
    (lowerSaddleGridBase_tendsto_atTop hd hm hθ C).eventually (eventually_ge_atTop (1 : ℝ))]
    with x hx hM hb
  have hMnat : 1 ≤ lowerSaddleM m x := by exact_mod_cast hM
  have hf := log_factorial_succ_lower (lowerSaddleM m x) hMnat
  have hω := (lowerSaddleOmega_rounding_bounds hd hb).1
  have hωmul := mul_le_mul_of_nonneg_left hω (show 0 ≤ (lowerSaddleM m x : ℝ) by positivity)
  have hbudget := lowerSaddleM_square_balance hm hθ hbalance hx.le
  rw [log_lowerSaddleEnergyTwo_ratio hd hCG (by linarith) τM]
  unfold lowerSaddleAliasUpper lowerSaddleOmegaZero at *
  nlinarith

theorem lowerSaddleAliasUpper_div_M_limit {d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C CG : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleAliasUpper s d m θ C CG τM x / lowerSaddleM m x)
      atTop (𝓝 ((d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
        2 * d * τ / (d + 4) + Real.log CG + 1 - C)) := by
  have hω := (lowerSaddleOmega_div_M_limit hd hm hθ C).const_mul
    ((d ^ 2 - 16 * s) / (d * (d + 4)))
  have hτ := (((lowerSaddleTau_limit hm hcontrol).const_mul (2 * d)).div_const (d + 4)).add_const
    (Real.log CG + 1 - C)
  have hh := hω.add hτ
  have hid : (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
      (2 * d * τ / (d + 4) + (Real.log CG + 1 - C)) =
      (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
        2 * d * τ / (d + 4) + Real.log CG + 1 - C := by ring
  rw [hid] at hh
  refine hh.congr' ?_
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  unfold lowerSaddleAliasUpper
  field_simp
  ring

/-- The genuine alias energy is negligible relative to the squared activity. -/
theorem lowerSaddleEnergyTwo_ratio_tends_zero {s d m θ C CG τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG)
    (hcontrol : LowerExponentControl τM τ Cτ)
    (hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4))))
    (hC : 1 + Real.log CG + (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
      2 * d * τ / (d + 4) < C) :
    Tendsto (fun x : ℝ => lowerSaddleEnergyTwo s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
  have hu := tendsto_atBot_of_div_negative (lowerSaddleM_tendsto_atTop hm)
    (lowerSaddleAliasUpper_div_M_limit hd hm hθ hcontrol s C CG) (by linarith)
  have hb := Real.tendsto_exp_atBot.comp hu
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hH := lowerSaddleH_positive d m θ C x
    have hN := lowerSaddleN_positive s d m θ C τM x
    have hA := lowerSaddleActivity_positive s d m θ C τM x
    unfold lowerSaddleEnergyTwo lowerSaddleMu
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_log_energyTwo_le_aliasUpper hd hm hθ hCG hbalance] with x hx hlog
    have hp : 0 < lowerSaddleEnergyTwo s d m θ C CG τM x /
        (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
      have hH := lowerSaddleH_positive d m θ C x
      have hN := lowerSaddleN_positive s d m θ C τM x
      have hA := lowerSaddleActivity_positive s d m θ C τM x
      unfold lowerSaddleEnergyTwo lowerSaddleMu
      positivity
    change _ ≤ Real.exp (lowerSaddleAliasUpper s d m θ C CG τM x)
    exact (Real.exp_log hp).symm.trans_le (Real.exp_le_exp.2 hlog)

theorem lowerSaddleD_div_M_limit {d m : ℝ} (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleD d m x : ℝ) / lowerSaddleM m x)
      atTop (𝓝 ((d + 8) / 4)) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hu : Tendsto (fun x : ℝ => 1 / (lowerSaddleM m x : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using! ht.inv_tendsto_atTop
  have herr : Tendsto (fun x : ℝ =>
      ((lowerSaddleD d m x : ℝ) - (d + 8) / 4 * lowerSaddleM m x) / lowerSaddleM m x)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) hu
    · exact div_nonneg (sub_nonneg.2 (Nat.le_ceil _)) (by positivity)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      have hc : 0 ≤ (d + 8) / 4 * (lowerSaddleM m x : ℝ) := by positivity
      have hh := Nat.ceil_lt_add_one hc
      change (lowerSaddleD d m x : ℝ) < (d + 8) / 4 * lowerSaddleM m x + 1 at hh
      linarith
  have hh := (tendsto_const_nhds (x := (d + 8) / 4)).add herr
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  field_simp
  ring

theorem log_lowerSaddleEnergyThree_ratio {s d m θ C CG x : ℝ}
    (hd : 0 < d) (hCG : 0 < CG) (hx : 0 < x) (τM : ℕ → ℝ) :
    Real.log (lowerSaddleEnergyThree s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) =
      (1 - 4 * s / d) * Real.log x - 4 * s / d * lowerSaddleOmega d m θ C x +
      (lowerSaddleD d m x : ℝ) * (Real.log CG - lowerSaddleOmega d m θ C x) -
        Real.log ((lowerSaddleD d m x + 1).factorial : ℝ) := by
  have hMu : 0 < lowerSaddleMu d m θ C x := by
    unfold lowerSaddleMu
    exact mul_pos hx (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
  have hA := lowerSaddleActivity_positive s d m θ C τM x
  have hH := lowerSaddleH_positive d m θ C x
  unfold lowerSaddleEnergyThree
  rw [Real.log_div (by positivity) (pow_ne_zero 2 hA.ne'),
    Real.log_div (by positivity) (by positivity)]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow hH, Real.log_pow, Real.log_pow, Real.log_mul hCG.ne' hMu.ne',
    lowerSaddleMu_eq_exp hx, Real.log_exp, lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  field_simp
  ring

def lowerSaddleCountUpper (s d m θ C CG x : ℝ) : ℝ :=
  (1 - 4 * s / d) * Real.log x +
    (lowerSaddleD d m x : ℝ) * (Real.log CG - lowerSaddleOmega d m θ C x)

theorem eventually_log_energyThree_le_countUpper {s d m θ C CG : ℝ} {τM : ℕ → ℝ}
    (hs : 0 ≤ s) (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG) :
    ∀ᶠ x : ℝ in atTop,
      Real.log (lowerSaddleEnergyThree s d m θ C CG τM x /
        (lowerSaddleActivity s d m θ C τM x) ^ 2) ≤ lowerSaddleCountUpper s d m θ C CG x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (lowerSaddleOmega_tendsto_atTop hd hm hθ C).eventually (eventually_ge_atTop (0 : ℝ))]
    with x hx hω
  rw [log_lowerSaddleEnergyThree_ratio hd hCG hx τM]
  have hf : 0 ≤ Real.log ((lowerSaddleD d m x + 1).factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (lowerSaddleD d m x + 1))
  unfold lowerSaddleCountUpper
  have hp : 0 ≤ 4 * s / d * lowerSaddleOmega d m θ C x := by positivity
  linarith

theorem lowerSaddleCountUpper_div_log_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (s C CG : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleCountUpper s d m θ C CG x / Real.log x)
      atTop (𝓝 (1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2)) := by
  have hD := lowerSaddleD_div_M_limit hd hm
  have hω := lowerSaddleOmega_div_M_limit hd hm hθ C
  have hM := lowerSaddleM_sq_div_log_limit hm
  have hconst : Tendsto (fun x : ℝ => Real.log CG / (lowerSaddleM m x : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using! (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log CG)
  have hh := (tendsto_const_nhds (x := 1 - 4 * s / d)).add
    ((hD.mul (hconst.sub hω)).mul hM)
  have hid : 1 - 4 * s / d + ((d + 8) / 4 * (0 - θ) * m ^ 2) =
      1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2 := by ring
  rw [hid] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx hMpos
  unfold lowerSaddleCountUpper
  field_simp [(Real.log_pos hx).ne']

/-- The genuine high-count factorial energy is negligible relative to squared activity. -/
theorem lowerSaddleEnergyThree_ratio_tends_zero {s d m θ C CG : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG)
    (hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4)))) :
    Tendsto (fun x : ℝ => lowerSaddleEnergyThree s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hc : 1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2 < 0 := by
    rw [mul_assoc ((d + 8) / 4), hbalance]
    have hid : 1 - 4 * s / d - (d + 8) / 4 * (4 * ((d - 4 * s) / (d * (d + 4)))) =
      -4 * ((d - 4 * s) / (d * (d + 4))) := by field_simp; ring
    rw [hid]
    have hp : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
    linarith
  have hu := tendsto_atBot_of_div_negative Real.tendsto_log_atTop
    (lowerSaddleCountUpper_div_log_limit hd0 hm hθ s C CG) hc
  have hb := Real.tendsto_exp_atBot.comp hu
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hH := lowerSaddleH_positive d m θ C x
    have hA := lowerSaddleActivity_positive s d m θ C τM x
    unfold lowerSaddleEnergyThree lowerSaddleMu
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_log_energyThree_le_countUpper (s := s) (τM := τM)
        (by linarith) hd0 hm hθ hCG] with x hx hlog
    have hp : 0 < lowerSaddleEnergyThree s d m θ C CG τM x /
        (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
      have hH := lowerSaddleH_positive d m θ C x
      have hA := lowerSaddleActivity_positive s d m θ C τM x
      unfold lowerSaddleEnergyThree lowerSaddleMu
      positivity
    change _ ≤ Real.exp (lowerSaddleCountUpper s d m θ C CG x)
    exact (Real.exp_log hp).symm.trans_le (Real.exp_le_exp.2 hlog)

/-- The combined explicit numerical energy envelope is at most `3 CG B²` eventually. -/
theorem eventually_lowerSaddle_numeric_cost {s d m θ C CG τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hCG : 0 < CG)
    (hcontrol : LowerExponentControl τM τ Cτ)
    (hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4))))
    (hC : 1 + Real.log CG + (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
      2 * d * τ / (d + 4) < C) :
    ∀ᶠ x : ℝ in atTop,
      CG * ((lowerSaddleActivity s d m θ C τM x) ^ 2 +
        lowerSaddleEnergyOne s d m θ C τM x + lowerSaddleEnergyTwo s d m θ C CG τM x +
        lowerSaddleEnergyThree s d m θ C CG τM x) ≤
          3 * CG * (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
  have hd0 : 0 < d := by linarith
  have htwo := lowerSaddleEnergyTwo_ratio_tends_zero hd0 hm hθ hCG hcontrol hbalance hC
  have hthree := lowerSaddleEnergyThree_ratio_tends_zero (C := C) (τM := τM) hs hd hm hθ hCG hbalance
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htwo.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hthree.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx h2 h3
  have hA : 0 < (lowerSaddleActivity s d m θ C τM x) ^ 2 :=
    sq_pos_of_pos (lowerSaddleActivity_positive s d m θ C τM x)
  have h2' := (div_lt_iff₀ hA).1 h2
  have h3' := (div_lt_iff₀ hA).1 h3
  rw [lowerSaddleEnergyOne_eq_activity_sq hd0 (by linarith) hx τM]
  calc
    _ ≤ CG * (3 * (lowerSaddleActivity s d m θ C τM x) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [h2', h3']) hCG.le
    _ = _ := by ring

theorem lowerSaddleRisk_residual_identity {s d m θ C cf τ x : ℝ} (τM : ℕ → ℝ)
    (hs : 1 < s) (hd : 4 * s < d) (hcf : 0 < cf)
    (hθrelation : 2 * (s - 1) * θ = d * τ) :
    Real.log (lowerSaddleRisk s d m θ C cf τM x) -
      rateLog (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x =
      (2 * Real.log cf - 2 * (s - 1) / (d + 4) * C) -
      (2 * d * τ / (d + 4)) * ((lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x)) +
      (2 * (s - 1) / (d + 4)) * (Real.log (lowerSaddleM m x) - Real.log (Real.log x) / 2) -
      (2 * (s - 1) / (d + 4)) * (lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x) -
      (d / (d + 4)) * ((τM (lowerSaddleM m x) - τ) * lowerSaddleM m x) := by
  have hsm : 2 * (s - 1) ≠ 0 := by linarith
  have hθeq : θ = d * τ / (2 * (s - 1)) :=
    (eq_div_iff hsm).2 (by simpa only [mul_comm] using hθrelation)
  rw [log_lowerSaddleRisk hs hd hcf τM]
  unfold rateLog lowerLogPower lowerSaddleOmegaZero
  rw [hθeq]
  field_simp [show s - 1 ≠ 0 by linarith, show d + 4 ≠ 0 by linarith]
  ring

theorem lowerSaddleRisk_residual_isBigO {s d m θ C cf τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hcontrol : LowerExponentControl τM τ Cτ) (hθrelation : 2 * (s - 1) * θ = d * τ) :
    (fun x : ℝ => Real.log (lowerSaddleRisk s d m θ C cf τM x) -
      rateLog (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have hd0 : 0 < d := by linarith
  have hceil : (fun x : ℝ => (lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (sub_nonneg.2 (lowerSaddleM_rounding hm.le).1)]
    linarith [(lowerSaddleM_rounding (x := x) hm.le).2]
  have hlog := (log_lowerSaddleM_residual_limit hm).isBigO_one ℝ
  have hω := (lowerSaddleOmega_rounding_limit hd0 hm hθ C).isBigO_one ℝ
  have hτ : (fun x : ℝ => (τM (lowerSaddleM m x) - τ) * lowerSaddleM m x)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound Cτ
    filter_upwards [(lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol] with x hx
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.2 hx.1) (by positivity))]
    exact hx.2
  have hc := Asymptotics.isBigO_const_one
    (2 * Real.log cf - 2 * (s - 1) / (d + 4) * C) (atTop : Filter ℝ) (F := ℝ)
  have hh := (((hc.sub (hceil.const_mul_left (2 * d * τ / (d + 4)))).add
    (hlog.const_mul_left (2 * (s - 1) / (d + 4)))).sub
    (hω.const_mul_left (2 * (s - 1) / (d + 4)))).sub (hτ.const_mul_left (d / (d + 4)))
  exact hh.congr_left (fun x => (lowerSaddleRisk_residual_identity τM hs hd hcf hθrelation).symm)

/-- The actual rounded numeric risk is comparable to the exact displayed saddle scale. -/
theorem eventually_lowerSaddleRisk_rate_bracket {s d m θ C cf τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hcontrol : LowerExponentControl τM τ Cτ) (hθrelation : 2 * (s - 1) * θ = d * τ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x ≤
        lowerSaddleRisk s d m θ C cf τM x ∧
      lowerSaddleRisk s d m θ C cf τM x ≤
        A * rateScale (rateExponent s d) (2 * d * τ / (d + 4) * m) (lowerLogPower s d) x := by
  obtain ⟨K, hK⟩ := (lowerSaddleRisk_residual_isBigO hs hd hm hθ hcf hcontrol hθrelation).bound
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _, Real.exp_pos _, ?_⟩
  filter_upwards [hK] with x hx
  simp only [Real.norm_eq_abs, norm_one, mul_one] at hx
  have hp := lowerSaddleRisk_positive (s := s) (d := d) (m := m) (θ := θ) (C := C) (x := x) hcf τM
  rcases abs_le.1 hx with ⟨hl, hu⟩
  unfold rateScale
  rw [← Real.exp_add, ← Real.exp_add]
  constructor
  · rw [← Real.exp_log hp]
    exact Real.exp_le_exp.2 ((le_sub_iff_add_le).1 hl)
  · rw [← Real.exp_log hp]
    exact Real.exp_le_exp.2 ((sub_le_iff_le_add).1 hu)

def lowerSaddleTheta (s d τ : ℝ) : ℝ := d * τ / (2 * (s - 1))

def lowerSaddleGamma (s d : ℝ) : ℝ := (d - 4 * s) / (d * (d + 4))

theorem lowerSaddleCoefficient_pos {s d τ : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) :
    0 < lowerSaddleCoefficient s d τ := by
  have hd0 : 0 < d := by linarith
  unfold lowerSaddleCoefficient
  apply Real.sqrt_pos.2
  positivity

theorem lowerSaddleTheta_pos {s d τ : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) : 0 < lowerSaddleTheta s d τ := by
  have hd0 : 0 < d := by linarith
  unfold lowerSaddleTheta
  positivity

theorem lowerSaddleTheta_relation {s d τ : ℝ} (hs : 1 < s) :
    2 * (s - 1) * lowerSaddleTheta s d τ = d * τ := by
  unfold lowerSaddleTheta
  field_simp [show s - 1 ≠ 0 by linarith]

theorem lowerSaddle_canonical_balance {s d τ : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) :
    lowerSaddleTheta s d τ * (lowerSaddleCoefficient s d τ) ^ 2 =
      4 * ((d - 4 * s) / (d * (d + 4))) := by
  have hd0 : 0 < d := by linarith
  have hp : 0 ≤ 8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ) := by positivity
  unfold lowerSaddleTheta lowerSaddleCoefficient
  rw [Real.sq_sqrt hp]
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

/-- The exact shrunk-endpoint exponent supplies the saddle's fixed control hypothesis. -/
theorem exists_actual_lowerExponentControl {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ Cτ : ℝ, 0 ≤ Cτ ∧ LowerExponentControl (shrunkDensityExponent a b)
      (densityIntervalExponent a b) Cτ := exists_shrunkDensityExponent_control ha hab

/-- With all the paper's fixed constants substituted, the actual risk has its displayed rate. -/
theorem actual_lowerSaddleRisk_rate_bracket {s d a b cf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hcf : 0 < cf) (C : ℝ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x ≤
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ∧
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ≤
      A * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hh := eventually_lowerSaddleRisk_rate_bracket (C := C)
    hs hd (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ) hcf hcontrol
    (lowerSaddleTheta_relation hs)
  rw [lower_saddle_stretchConstant hs hd hτ] at hh
  exact hh

theorem log_lowerSaddleEta_div_log_limit {s d m θ cf : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf) (C : ℝ) :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleEta s d m θ C cf x) / Real.log x)
      atTop (𝓝 (-s / d)) := by
  have hconst := tendsto_const_div_log (Real.log cf)
  have hω := lowerSaddleOmega_div_log_limit hd hm hθ C
  have hh := hconst.sub (((tendsto_const_nhds (x := (1 : ℝ))).add hω).const_mul (s / d))
  simp only [add_zero, mul_one, zero_sub, ← neg_div] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  unfold lowerSaddleEta
  rw [Real.log_mul hcf.ne' (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s).ne',
    Real.log_rpow (lowerSaddleH_positive d m θ C x), lowerSaddleH_eq_exp hd.ne', Real.log_exp]
  field_simp [(Real.log_pos hx).ne']
  ring

def lowerSaddleResponseQuantity (s d m θ C cf : ℝ) (q : ℕ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ (4 * q) * (lowerSaddleN s d m θ C τM x) ^ d

theorem lowerSaddleResponseQuantity_tends_zero {s d m θ cf τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hcontrol : LowerExponentControl τM τ Cτ) (q : ℕ) (hq : d / (4 * s) - 1 ≤ (q : ℝ)) (C : ℝ) :
    Tendsto (lowerSaddleResponseQuantity s d m θ C cf q τM) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hs0 : 0 < s := by linarith
  have hγ : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
  have hqmul : d ≤ 4 * s * ((q : ℝ) + 1) := by
    have hh : d / (4 * s) ≤ (q : ℝ) + 1 := by linarith
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 4 * s)).1 hh
  have hc : (4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))) < 0 := by
    have hid : (4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))) =
        -4 * ((d - 4 * s) / (d * (d + 4))) + (d - 4 * s * ((q : ℝ) + 1)) / d := by
      field_simp
      ring
    rw [hid]
    have hn : (d - 4 * s * ((q : ℝ) + 1)) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd0.le
    linarith
  have hh := ((log_lowerSaddleEta_div_log_limit (s := s) hd0 hm hθ hcf C).const_mul
    ((4 : ℝ) * (q : ℝ))).add
    ((lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C).const_mul d)
  have hlog : Tendsto (fun x : ℝ => Real.log (lowerSaddleResponseQuantity s d m θ C cf q τM x) / Real.log x)
      atTop (𝓝 ((4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))))) := by
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hEta : 0 < lowerSaddleEta s d m θ C cf x :=
      mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)
    unfold lowerSaddleResponseQuantity
    rw [Real.log_mul (pow_ne_zero (4 * q) hEta.ne')
      (Real.rpow_pos_of_pos (lowerSaddleN_positive s d m θ C τM x) d).ne',
      Real.log_pow, Real.log_rpow (lowerSaddleN_positive s d m θ C τM x)]
    push_cast
    ring
  have ht := tendsto_atBot_of_div_negative Real.tendsto_log_atTop hlog hc
  have h := Real.tendsto_exp_atBot.comp ht
  exact h.congr (fun x => Real.exp_log (by
    unfold lowerSaddleResponseQuantity lowerSaddleEta
    have hH := lowerSaddleH_positive d m θ C x
    have hN := lowerSaddleN_positive s d m θ C τM x
    positivity))

def lowerSaddleResponseOrder (s d : ℝ) : ℕ := max 2 (Nat.floor (d / (4 * s)))

theorem lowerSaddleResponseOrder_bound {s d : ℝ} (_hs : 0 < s) (_hd : 0 ≤ d) :
    d / (4 * s) - 1 ≤ (lowerSaddleResponseOrder s d : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (d / (4 * s))
  have hmax : (Nat.floor (d / (4 * s)) : ℝ) ≤ lowerSaddleResponseOrder s d := by
    exact_mod_cast le_max_right 2 (Nat.floor (d / (4 * s)))
  linarith

/-- The complete numerical regime of `eq:LB-regime`, for the actual saddle tuple. -/
def LowerSaddleReg (K η0 s d m θ C cf : ℝ) (M0 : ℕ) (τM : ℕ → ℝ) (x : ℝ) : Prop :=
  M0 ≤ lowerSaddleM m x ∧
  lowerSaddleD d m x = Nat.ceil ((d + 8) / 4 * lowerSaddleM m x) ∧
  1 ≤ lowerSaddleN s d m θ C τM x ∧
  0 < lowerSaddleMu d m θ C x ∧ lowerSaddleMu d m θ C x < 1 ∧
  (lowerSaddleM m x : ℝ) / K ≤ lowerSaddleOmega d m θ C x ∧
  lowerSaddleOmega d m θ C x ≤ K * lowerSaddleM m x ∧
  (lowerSaddleM m x : ℝ) ^ 2 / K ≤ Real.log (lowerSaddleN s d m θ C τM x) ∧
  Real.log (lowerSaddleN s d m θ C τM x) ≤ K * (lowerSaddleM m x : ℝ) ^ 2 ∧
  0 < lowerSaddleEta s d m θ C cf x ∧ lowerSaddleEta s d m θ C cf x ≤ η0 ∧
  lowerSaddleResponseQuantity s d m θ C cf (lowerSaddleResponseOrder s d) τM x ≤ 1

theorem eventually_lowerSaddleReg {K η0 s d m θ cf τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ) (hcf : 0 < cf)
    (hη0 : 0 < η0) (_hK : 1 ≤ K) (hcontrol : LowerExponentControl τM τ Cτ)
    (hθlow : 1 / K < θ) (hθhigh : θ < K)
    (hNlow : 1 / K < ((d - 4 * s) / (d * (d + 4))) / m ^ 2)
    (hNhigh : ((d - 4 * s) / (d * (d + 4))) / m ^ 2 < K) (C : ℝ) (M0 : ℕ) :
    ∀ᶠ x : ℝ in atTop, LowerSaddleReg K η0 s d m θ C cf M0 τM x := by
  have hd0 : 0 < d := by linarith
  have hM := lowerSaddleM_tendsto_atTop hm
  have hω := lowerSaddleOmega_div_M_limit hd0 hm hθ C
  have hN := lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C
  have hrsp := lowerSaddleResponseQuantity_tends_zero hs hd hm hθ hcf hcontrol
    (lowerSaddleResponseOrder s d) (lowerSaddleResponseOrder_bound (by linarith) hd0.le) C
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop M0),
    hM.eventually (eventually_gt_atTop (0 : ℝ)),
    (lowerSaddleN_tendsto_atTop hs hd hm hθ hcontrol C).eventually (eventually_ge_atTop (1 : ℝ)),
    (lowerSaddleMu_tends_zero hd0 hm hθ C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hω.eventually (lt_mem_nhds hθlow), hω.eventually (gt_mem_nhds hθhigh),
    hN.eventually (lt_mem_nhds hNlow), hN.eventually (gt_mem_nhds hNhigh),
    (lowerSaddleEta_tends_zero (s := s) (by linarith) hd0 hm hθ C cf).eventually (gt_mem_nhds hη0),
    hrsp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with x hx hM0 hMpos hN1 hMu1 hωl hωu hNl hNu hEta0 hRsp
  have hMu : 0 < lowerSaddleMu d m θ C x := by
    unfold lowerSaddleMu
    exact mul_pos hx (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
  have hEta : 0 < lowerSaddleEta s d m θ C cf x :=
    mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)
  have hωl' := (lt_div_iff₀ hMpos).1 hωl
  have hωu' := (div_lt_iff₀ hMpos).1 hωu
  have hNl' := (lt_div_iff₀ (sq_pos_of_pos hMpos)).1 hNl
  have hNu' := (div_lt_iff₀ (sq_pos_of_pos hMpos)).1 hNu
  refine ⟨hM0, rfl, hN1, hMu, hMu1, ?_, hωu'.le, ?_, hNu'.le, hEta, hEta0.le, hRsp.le⟩
  · simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hωl'.le
  · simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hNl'.le

/-- The remaining fixed grid and mass hypotheses of `lem:score-risk` hold eventually. -/
theorem eventually_lowerSaddle_grid_and_mass {d m θ cm Cmgf : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) (hCmgf : 0 < Cmgf)
    (C : ℝ) (gridThreshold : ℕ) :
    ∀ᶠ x : ℝ in atTop, gridThreshold ≤ lowerSaddleGrid d m θ C x ∧
      8 * Cmgf * lowerSaddleMu d m θ C x ≤ cm / lowerSaddleM m x := by
  have hgrid : Tendsto (lowerSaddleGrid d m θ C) atTop atTop :=
    tendsto_natCast_atTop_iff.1 (lowerSaddleGrid_tendsto_atTop hd hm hθ C)
  have hcap : 0 < cm / (8 * Cmgf) := by positivity
  filter_upwards [hgrid.eventually (eventually_ge_atTop gridThreshold),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
    (lowerSaddleM_mul_mu_tends_zero hd hm hθ C).eventually (gt_mem_nhds hcap)] with x hx hM hmass
  refine ⟨hx, (le_div_iff₀ hM).2 ?_⟩
  have hh := (lt_div_iff₀ (by positivity : 0 < 8 * Cmgf)).1 hmass
  nlinarith only [hh]

theorem tendsto_sample_div_log : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  have hh : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_power_div_sample 1
  have hwithin : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hh, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  exact hwithin.inv_tendsto_nhdsGT_zero.congr (fun x => by
    change (Real.log x / x)⁻¹ = x / Real.log x
    rw [inv_div])

/-- The mass-tail envelope is negligible compared with the square of every displayed rate. -/
theorem exponential_sample_log_tail_over_rate_tends_zero {c : ℝ} (hc : 0 < c) (lam κ a : ℝ) :
    Tendsto (fun x : ℝ => 2 * Real.exp (-c * x / Real.log x) / (rateScale lam κ a x) ^ 2)
      atTop (𝓝 0) := by
  have hs := tendsto_sample_div_log
  have hconst : Tendsto (fun x : ℝ => Real.log 2 / (x / Real.log x)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using! hs.inv_tendsto_atTop.const_mul (Real.log 2)
  have hrate : Tendsto (fun x : ℝ => rateLog lam κ a x / Real.log x) atTop (𝓝 (-lam)) := by
    have hh := (tendsto_normalized_log_scale lam κ a 0).neg
    convert! hh using 1
    funext x
    ring
  have hsq : Tendsto (fun x : ℝ => (Real.log x) ^ (2 : ℕ) / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using tendsto_log_power_div_sample 2
  have hcorr : Tendsto (fun x : ℝ => rateLog lam κ a x / (x / Real.log x)) atTop (𝓝 0) := by
    have hh := hrate.mul hsq
    simp only [mul_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    field_simp [(Real.log_pos hx).ne']
  have hh := (hconst.sub (tendsto_const_nhds (x := c))).sub (hcorr.const_mul 2)
  simp only [zero_sub, mul_zero, sub_zero] at hh
  have hlog : Tendsto (fun x : ℝ =>
      (Real.log 2 - c * x / Real.log x - 2 * rateLog lam κ a x) / (x / Real.log x))
      atTop (𝓝 (-c)) := by
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    field_simp [(Real.log_pos hx).ne']
  have ht := tendsto_atBot_of_div_negative hs hlog (neg_neg_of_pos hc)
  have h := Real.tendsto_exp_atBot.comp ht
  refine h.congr (fun x => ?_)
  change Real.exp (Real.log 2 - c * x / Real.log x - 2 * rateLog lam κ a x) = _
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  unfold rateScale
  rw [show 2 * rateLog lam κ a x = ((2 : ℕ) : ℝ) * rateLog lam κ a x by rfl, Real.exp_nat_mul]
  rw [show -c * x / Real.log x = -(c * x / Real.log x) by ring, Real.exp_neg]
  ring

def lowerSaddleExceptionalTail (d m θ C c x : ℝ) : ℝ :=
  2 * Real.exp (-c / ((lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d))

theorem eventually_lowerSaddle_mass_variance_bound {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d ≤
        2 * m ^ 2 * Real.log x / x := by
  have hsq := lowerSaddleM_sq_div_log_limit hm
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hsq.eventually (gt_mem_nhds (by nlinarith : m ^ 2 < 2 * m ^ 2)),
    (lowerSaddleMu_tends_zero hd hm hθ C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with x hx hM hMu
  have hx0 : 0 < x := by linarith
  have hH : (lowerSaddleH d m θ C x) ^ d ≤ 1 / x := by
    apply (le_div_iff₀ hx0).2
    unfold lowerSaddleMu at hMu
    simpa only [mul_comm] using hMu.le
  have hM' := (div_lt_iff₀ (Real.log_pos hx)).1 hM
  calc
    _ ≤ (lowerSaddleM m x : ℝ) ^ 2 * (1 / x) := mul_le_mul_of_nonneg_left hH (sq_nonneg _)
    _ ≤ 2 * m ^ 2 * Real.log x / x := by
      simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using
        mul_le_mul_of_nonneg_right hM'.le (inv_nonneg.2 hx0.le)

theorem eventually_lowerSaddle_exceptionalTail_envelope {d m θ c : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hc : 0 < c) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, lowerSaddleExceptionalTail d m θ C c x ≤
      2 * Real.exp (-(c / (2 * m ^ 2)) * x / Real.log x) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_lowerSaddle_mass_variance_bound hd hm hθ C] with x hx hM hbound
  have hx0 : 0 < x := by linarith
  have hden : 0 < (lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d :=
    mul_pos (sq_pos_of_pos hM) (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
  have hh := div_le_div_of_nonneg_left hc.le hden hbound
  have hid : c / (2 * m ^ 2 * Real.log x / x) = (c / (2 * m ^ 2)) * x / Real.log x := by field_simp
  rw [hid] at hh
  unfold lowerSaddleExceptionalTail
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.2
  convert neg_le_neg hh using 1 <;> ring

/-- The paper's actual mass exception is `o(Psi²)`, without an exceptional-tail hypothesis. -/
theorem lowerSaddleExceptionalTail_over_rate_tends_zero {d m θ c : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hc : 0 < c) (C lam κ a : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleExceptionalTail d m θ C c x / (rateScale lam κ a x) ^ 2)
      atTop (𝓝 0) := by
  have hb := exponential_sample_log_tail_over_rate_tends_zero
    (show 0 < c / (2 * m ^ 2) by positivity) lam κ a
  apply squeeze_zero' (Eventually.of_forall fun x => by
    unfold lowerSaddleExceptionalTail rateScale
    positivity) _ hb
  filter_upwards [eventually_lowerSaddle_exceptionalTail_envelope hd hm hθ hc C] with x hx
  exact div_le_div_of_nonneg_right hx (sq_nonneg _)

theorem lowerSaddleGridBase_eq_source {d m θ C x : ℝ} (hx : 0 < x) :
    lowerSaddleGridBase d m θ C x = (x * Real.exp (lowerSaddleOmegaZero m θ C x)) ^ (1 / d) := by
  unfold lowerSaddleGridBase
  rw [Real.rpow_def_of_pos (mul_pos hx (Real.exp_pos _)),
    Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
  congr 1
  ring

/-- Every fixed positive pair of limits lies strictly inside one fixed `Reg(K)` window. -/
theorem exists_regime_window {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∃ K : ℝ, 1 ≤ K ∧ 1 / K < u ∧ u < K ∧ 1 / K < v ∧ v < K := by
  let K := 2 + u + v + 1 / u + 1 / v
  have huinv : 0 < 1 / u := by positivity
  have hvinv : 0 < 1 / v := by positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have h1u : 1 / u < K := by dsimp [K]; linarith
  have h1v : 1 / v < K := by dsimp [K]; linarith
  refine ⟨K, ?_, (div_lt_iff₀ hK).2 ?_, ?_, (div_lt_iff₀ hK).2 ?_, ?_⟩
  · dsimp [K]; linarith
  · have hh := mul_lt_mul_of_pos_left h1u hu
    simpa only [one_div, mul_inv_cancel₀ hu.ne'] using hh
  · dsimp [K]; linarith
  · have hh := mul_lt_mul_of_pos_left h1v hv
    simpa only [one_div, mul_inv_cancel₀ hv.ne'] using hh
  · dsimp [K]; linarith

/-- A fixed `K` works for the actual shrunk endpoints and every later fixed threshold. -/
theorem actual_lowerSaddle_fixed_regime_window {s d a b cf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hcf : 0 < cf) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (C η0 : ℝ) (M0 : ℕ), 0 < η0 →
      ∀ᶠ x : ℝ in atTop,
        LowerSaddleReg K η0 s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
          (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf M0 (shrunkDensityExponent a b) x := by
  have hτ := densityIntervalExponent_pos ha hab
  have hm := lowerSaddleCoefficient_pos hs hd hτ
  have hθ := lowerSaddleTheta_pos hs hd hτ
  have hd0 : 0 < d := by linarith
  have hγm : 0 < ((d - 4 * s) / (d * (d + 4))) /
      (lowerSaddleCoefficient s d (densityIntervalExponent a b)) ^ 2 := by positivity
  obtain ⟨K, hK, hθl, hθu, hNl, hNu⟩ := exists_regime_window hθ hγm
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  refine ⟨K, hK, fun C η0 M0 hη0 => ?_⟩
  exact eventually_lowerSaddleReg hs hd hm hθ hcf hη0 hK hcontrol hθl hθu hNl hNu C M0

/-- The numerical cost estimate for the exact source parameters, including actual `τ_M`. -/
theorem eventually_actual_lowerSaddle_numeric_cost {s d a b CG C : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hCG : 0 < CG)
    (hC : 1 + Real.log CG + (d ^ 2 - 16 * s) / (d * (d + 4)) *
      lowerSaddleTheta s d (densityIntervalExponent a b) +
      2 * d * densityIntervalExponent a b / (d + 4) < C) :
    ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let τM := shrunkDensityExponent a b
      CG * ((lowerSaddleActivity s d m θ C τM x) ^ 2 + lowerSaddleEnergyOne s d m θ C τM x +
        lowerSaddleEnergyTwo s d m θ C CG τM x + lowerSaddleEnergyThree s d m θ C CG τM x) ≤
          3 * CG * (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerSaddle_numeric_cost hs hd (lowerSaddleCoefficient_pos hs hd hτ)
    (lowerSaddleTheta_pos hs hd hτ) hCG hcontrol (lowerSaddle_canonical_balance hs hd hτ) hC

/-- `epsilon_n` with the source's mass-tail coefficient is `o(Psi²)`. -/
theorem actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero {s d a b cm Cmgf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b)
    (hcm : 0 < cm) (hCmgf : 0 < Cmgf) (C : ℝ) :
    Tendsto (fun x : ℝ =>
      lowerSaddleExceptionalTail d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C (cm ^ 2 / (8 * Cmgf)) x /
        (rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
          (lowerLogPower s d) x) ^ 2) atTop (𝓝 0) := by
  have hτ := densityIntervalExponent_pos ha hab
  exact lowerSaddleExceptionalTail_over_rate_tends_zero (by linarith)
    (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ)
    (by positivity) C (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b)) (lowerLogPower s d)

end NearlyMinimax
