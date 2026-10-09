module

public import Mathlib


@[expose] public section

/-!
# The actual all-sample low-smoothness grid allocation

The grid is `k=ceil(4 n^(2/(d+4s)))` and its field amplitude is
`eta=b/k^s`. For `d>=4s`, its design occupancy is at most one, its
numeric score energy is uniformly bounded by `b^4`, and its variance
separation has the exact lower polynomial rate. These are allocation
inequalities; the finite-prior statistical score and legality bridges are
proved separately.
-/

noncomputable section
namespace NearlyMinimax

def lowSmoothnessGridExponent (d : ℕ) (s : ℝ) : ℝ := 2 / ((d : ℝ) + 4 * s)

def lowSmoothnessGrid (d : ℕ) (s x : ℝ) : ℕ := Nat.ceil (4 * x ^ lowSmoothnessGridExponent d s)

def lowSmoothnessAmplitude (d : ℕ) (s b x : ℝ) : ℝ := b / (lowSmoothnessGrid d s x : ℝ) ^ s

theorem lowSmoothnessGridExponent_pos {d : ℕ} {s : ℝ} (hs : 0 < s) :
    0 < lowSmoothnessGridExponent d s := by
  unfold lowSmoothnessGridExponent
  positivity

theorem lowSmoothnessGrid_rounding {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    4 * x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) ∧
      (lowSmoothnessGrid d s x : ℝ) ≤ 5 * x ^ lowSmoothnessGridExponent d s := by
  have hbase : 1 ≤ x ^ lowSmoothnessGridExponent d s :=
    Real.one_le_rpow hx (lowSmoothnessGridExponent_pos hs).le
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * x ^ lowSmoothnessGridExponent d s by positivity)
  refine ⟨Nat.le_ceil _, ?_⟩
  change (lowSmoothnessGrid d s x : ℝ) < 4 * x ^ lowSmoothnessGridExponent d s + 1 at hc
  linarith

theorem lowSmoothnessGrid_ge_four {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    4 ≤ lowSmoothnessGrid d s x := by
  have hbase : 1 ≤ x ^ lowSmoothnessGridExponent d s :=
    Real.one_le_rpow hx (lowSmoothnessGridExponent_pos hs).le
  have hh := (lowSmoothnessGrid_rounding (d := d) hs hx).1
  exact_mod_cast (show (4 : ℝ) ≤ (lowSmoothnessGrid d s x : ℝ) by linarith)

theorem lowSmoothnessGrid_positive {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    0 < (lowSmoothnessGrid d s x : ℝ) := by
  have hh := lowSmoothnessGrid_ge_four (d := d) hs hx
  exact_mod_cast (by omega : 0 < lowSmoothnessGrid d s x)

theorem lowSmoothness_design_occupancy {d : ℕ} {s x : ℝ}
    (hs : 0 < s) (hd : 4 * s ≤ (d : ℝ)) (hx : 1 ≤ x) :
    x * (2 / (lowSmoothnessGrid d s x : ℝ)) ^ d ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hden : 0 < (d : ℝ) + 4 * s := by positivity
  have hpd : 1 ≤ lowSmoothnessGridExponent d s * d := by
    unfold lowSmoothnessGridExponent
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hden).2 (by linarith)
  have hxp : x ≤ x ^ (lowSmoothnessGridExponent d s * d) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hpd
  have hgrid := pow_le_pow_left₀ (by positivity) (lowSmoothnessGrid_rounding (d := d) hs hx).1 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hgrid
  have hpow : (2 : ℝ) ^ d ≤ (4 : ℝ) ^ d := by gcongr; norm_num
  have hbudget : x * (2 : ℝ) ^ d ≤ (lowSmoothnessGrid d s x : ℝ) ^ d := by
    calc
      _ ≤ x * (4 : ℝ) ^ d := mul_le_mul_of_nonneg_left hpow hx0.le
      _ ≤ (4 : ℝ) ^ d * x ^ (lowSmoothnessGridExponent d s * d) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxp (by positivity : 0 ≤ (4 : ℝ) ^ d)
      _ ≤ _ := hgrid
  rw [div_pow, ← mul_div_assoc]
  exact (div_le_iff₀ (pow_pos hk d)).2 (by simpa only [one_mul] using hbudget)

theorem lowSmoothnessAmplitude_nonneg {d : ℕ} {s b x : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hx : 1 ≤ x) : 0 ≤ lowSmoothnessAmplitude d s b x := by
  unfold lowSmoothnessAmplitude
  exact div_nonneg hb (Real.rpow_pos_of_pos (lowSmoothnessGrid_positive (d := d) hs hx) s).le

theorem lowSmoothnessAmplitude_le_budget {d : ℕ} {s b x : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hx : 1 ≤ x) : lowSmoothnessAmplitude d s b x ≤ b := by
  have hk : 1 ≤ (lowSmoothnessGrid d s x : ℝ) := by
    have hh := lowSmoothnessGrid_ge_four (d := d) hs hx
    exact_mod_cast (by omega : 1 ≤ lowSmoothnessGrid d s x)
  unfold lowSmoothnessAmplitude
  exact div_le_self hb (Real.one_le_rpow hk hs.le)

theorem lowSmoothness_grid_power_budget {d : ℕ} {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    x ^ (2 : ℕ) ≤ (lowSmoothnessGrid d s x : ℝ) ^ ((d : ℝ) + 4 * s) := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hden : 0 < (d : ℝ) + 4 * s := by positivity
  have hbase : x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) := by
    have hh := (lowSmoothnessGrid_rounding (d := d) hs hx).1
    have hp : 0 ≤ x ^ lowSmoothnessGridExponent d s := (Real.rpow_pos_of_pos hx0 _).le
    linarith
  have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos hx0 _).le hbase hden.le
  rw [← Real.rpow_mul hx0.le] at hh
  have heq : lowSmoothnessGridExponent d s * ((d : ℝ) + 4 * s) = 2 := by
    unfold lowSmoothnessGridExponent
    exact div_mul_cancel₀ _ hden.ne'
  rw [heq, Real.rpow_two] at hh
  exact hh

/-- The full source factor `n² eta⁴/k^d` is bounded uniformly for every `n>=1`. -/
theorem lowSmoothness_numeric_score_budget {d : ℕ} {s b x : ℝ}
    (hs : 0 < s) (_hb : 0 ≤ b) (hx : 1 ≤ x) :
    x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d ≤ b ^ 4 := by
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hbudget := lowSmoothness_grid_power_budget (d := d) hs hx
  have hid : x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d =
      b ^ 4 * (x ^ 2 / (lowSmoothnessGrid d s x : ℝ) ^ ((d : ℝ) + 4 * s)) := by
    unfold lowSmoothnessAmplitude
    have hp4 : ((lowSmoothnessGrid d s x : ℝ) ^ s) ^ (4 : ℕ) =
        (lowSmoothnessGrid d s x : ℝ) ^ (4 * s) := by
      rw [← Real.rpow_mul_natCast hk.le]
      congr 1
      norm_num
      ring
    rw [div_pow, hp4, Real.rpow_add hk, Real.rpow_natCast]
    field_simp
  rw [hid]
  have hh := (div_le_one (Real.rpow_pos_of_pos hk _)).2 hbudget
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ b ^ (4 : ℕ))

/-- The actual variance separation has the paper's all-sample polynomial lower rate. -/
theorem lowSmoothness_variance_separation {d : ℕ} {s b x : ℝ}
    (hs : 0 < s) (hx : 1 ≤ x) :
    b ^ 2 / (5 : ℝ) ^ (2 * s) * x ^ (-4 * s / ((d : ℝ) + 4 * s)) ≤
      (lowSmoothnessAmplitude d s b x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hbase := (lowSmoothnessGrid_rounding (d := d) hs hx).2
  have hupper := Real.rpow_le_rpow hk.le hbase (show 0 ≤ 2 * s by positivity)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (Real.rpow_pos_of_pos hx0 _).le,
    ← Real.rpow_mul hx0.le] at hupper
  have heq : lowSmoothnessGridExponent d s * (2 * s) = 4 * s / ((d : ℝ) + 4 * s) := by
    unfold lowSmoothnessGridExponent
    ring
  rw [heq] at hupper
  have hh := div_le_div_of_nonneg_left (sq_nonneg b) (Real.rpow_pos_of_pos hk _) hupper
  have hright : (lowSmoothnessAmplitude d s b x) ^ 2 = b ^ 2 / (lowSmoothnessGrid d s x : ℝ) ^ (2 * s) := by
    unfold lowSmoothnessAmplitude
    rw [div_pow, ← Real.rpow_mul_natCast hk.le]
    congr 2
    norm_num
    ring
  rw [hright]
  have hleft : b ^ 2 / ((5 : ℝ) ^ (2 * s) * x ^ (4 * s / ((d : ℝ) + 4 * s))) =
      b ^ 2 / (5 : ℝ) ^ (2 * s) * x ^ (-4 * s / ((d : ℝ) + 4 * s)) := by
    rw [show -4 * s / ((d : ℝ) + 4 * s) = -(4 * s / ((d : ℝ) + 4 * s)) by ring,
      Real.rpow_neg hx0.le]
    ring
  rw [← hleft]
  exact hh

theorem lowSmoothness_amplitude_legal_guards {d : ℕ} {s b x ρ : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hx : 1 ≤ x)
    (hlinear : ((2 : ℝ) ^ d + 2) * b ≤ ρ) (hsquare : b ^ 2 ≤ ρ) :
    0 ≤ lowSmoothnessAmplitude d s b x ∧
      ((2 : ℝ) ^ d + 2) * lowSmoothnessAmplitude d s b x ≤ ρ ∧
      (lowSmoothnessAmplitude d s b x) ^ 2 ≤ ρ := by
  have hn := lowSmoothnessAmplitude_nonneg (d := d) hs hb hx
  have hbnd := lowSmoothnessAmplitude_le_budget (d := d) hs hb hx
  refine ⟨hn, ?_, (pow_le_pow_left₀ hn hbnd 2).trans hsquare⟩
  exact (mul_le_mul_of_nonneg_left hbnd (by positivity : 0 ≤ (2 : ℝ) ^ d + 2)).trans hlinear

/-- A fixed source score multiplier `Q` produces a fixed all-sample energy budget. -/
theorem lowSmoothness_total_score_budget {d : ℕ} {s b x Q : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hx : 1 ≤ x) (hQ : 0 ≤ Q) :
    Q * (x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d) ≤ Q * b ^ 4 :=
  mul_le_mul_of_nonneg_left (lowSmoothness_numeric_score_budget hs hb hx) hQ

/-- A fixed amplitude smallness condition controls the integrated source score. -/
theorem lowSmoothness_integrated_score_budget {d : ℕ} {s b x Q : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hx : 1 ≤ x) (hQ : 0 ≤ Q)
    (hsmall : b ^ 2 * Real.sqrt Q ≤ 1) :
    Real.sqrt (Q * (x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 /
      (lowSmoothnessGrid d s x : ℝ) ^ d)) ≤ 1 := by
  have hh := Real.sqrt_le_sqrt (lowSmoothness_total_score_budget (d := d) hs hb hx hQ)
  have hid : Real.sqrt (Q * b ^ 4) = b ^ 2 * Real.sqrt Q := by
    rw [Real.sqrt_mul hQ, show b ^ (4 : ℕ) = (b ^ (2 : ℕ)) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg b)]
    ring
  rw [hid] at hh
  exact hh.trans hsmall

/-- The same rounded grid balances the concrete pair-estimator variance. -/
theorem lowSmoothnessGrid_pair_variance_budget {d : ℕ} {s x : ℝ}
    (hs : 0 < s) (hx : 1 ≤ x) :
    (lowSmoothnessGrid d s x : ℝ) ^ d / x ^ 2 ≤
      (5 : ℝ) ^ d * x ^ (-8 * s / ((d : ℝ) + 4 * s)) := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hupper := pow_le_pow_left₀ hk.le (lowSmoothnessGrid_rounding (d := d) hs hx).2 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hupper
  have heq : lowSmoothnessGridExponent d s * d - 2 = -8 * s / ((d : ℝ) + 4 * s) := by
    unfold lowSmoothnessGridExponent
    field_simp
    ring
  have hid : (5 : ℝ) ^ d * x ^ (lowSmoothnessGridExponent d s * d) / x ^ (2 : ℕ) =
      (5 : ℝ) ^ d * x ^ (-8 * s / ((d : ℝ) + 4 * s)) := by
    rw [← Real.rpow_two, mul_div_assoc, ← Real.rpow_sub hx0, heq]
  rw [← hid]
  exact div_le_div_of_nonneg_right hupper (sq_nonneg x)

theorem lowSmoothnessGrid_pair_bias_budget {d : ℕ} {s x : ℝ}
    (hs : 0 < s) (hx : 1 ≤ x) :
    (lowSmoothnessGrid d s x : ℝ) ^ (-4 * s) ≤ x ^ (-8 * s / ((d : ℝ) + 4 * s)) := by
  have hx0 : 0 < x := by linarith
  have hbase : x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) := by
    have hh := (lowSmoothnessGrid_rounding (d := d) hs hx).1
    have hp := Real.rpow_pos_of_pos hx0 (lowSmoothnessGridExponent d s)
    linarith
  have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx0 _) hbase (by linarith : -4 * s ≤ 0)
  rw [← Real.rpow_mul hx0.le] at hh
  have heq : lowSmoothnessGridExponent d s * (-4 * s) = -8 * s / ((d : ℝ) + 4 * s) := by
    unfold lowSmoothnessGridExponent
    ring
  rw [heq] at hh
  exact hh

end NearlyMinimax
