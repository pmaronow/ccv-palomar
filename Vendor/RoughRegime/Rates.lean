module

public import Mathlib


@[expose] public section

/-! Exact algebra of the rate parameters in Section 2. These theorems do not
assume or assert that the defined rate is the minimax risk. -/

noncomputable section

namespace RoughRegime.Rates

def rho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

def tau (lo hi : ℝ) : ℝ := -Real.log (rho lo hi)

def kappa (θ τ : ℝ) : ℝ := 2 * Real.sqrt (θ * (1 - 2 * θ) * τ)

def subcriticalScale (n θ τ : ℝ) : ℝ :=
  n ^ (-θ) * (Real.log n) ^ (θ / 2) * Real.exp (-kappa θ τ * Real.sqrt (Real.log n))

theorem rho_pos (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) : 0 < rho lo hi := by
  have hl : 0 < Real.sqrt lo := Real.sqrt_pos.mpr hlo
  have hh : Real.sqrt lo < Real.sqrt hi := Real.sqrt_lt_sqrt hlo.le hhi
  unfold rho
  exact div_pos (sub_pos.mpr hh) (by linarith)

theorem rho_lt_one (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) : rho lo hi < 1 := by
  have hl : 0 < Real.sqrt lo := Real.sqrt_pos.mpr hlo
  have hh : Real.sqrt lo < Real.sqrt hi := Real.sqrt_lt_sqrt hlo.le hhi
  unfold rho
  apply (div_lt_one (by linarith : 0 < Real.sqrt hi + Real.sqrt lo)).mpr
  linarith

theorem tau_pos (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) : 0 < tau lo hi := by
  unfold tau
  have h := Real.log_neg (rho_pos lo hi hlo hhi) (rho_lt_one lo hi hlo hhi)
  linarith

theorem kappa_pos (θ τ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1 / 2) (hτ : 0 < τ) :
    0 < kappa θ τ := by
  unfold kappa
  have h : 0 < θ * (1 - 2 * θ) * τ :=
    mul_pos (mul_pos hθ (by linarith)) hτ
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr h)

theorem scale_pos (n θ τ : ℝ) (hn : 1 < n) : 0 < subcriticalScale n θ τ := by
  unfold subcriticalScale
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (Real.log_pos hn) _)) (Real.exp_pos _)

/-- Exact logarithm of the common scale; no asymptotic remainder is suppressed. -/
theorem log_scale (n θ τ : ℝ) (hn : 1 < n) :
    Real.log (subcriticalScale n θ τ) =
      -θ * Real.log n + θ / 2 * Real.log (Real.log n) -
        kappa θ τ * Real.sqrt (Real.log n) := by
  have hn0 : 0 < n := by linarith
  have hln : 0 < Real.log n := Real.log_pos hn
  unfold subcriticalScale
  rw [Real.log_mul (mul_ne_zero (Real.rpow_pos_of_pos hn0 _).ne'
    (Real.rpow_pos_of_pos hln _).ne') (Real.exp_pos _).ne']
  rw [Real.log_mul (Real.rpow_pos_of_pos hn0 _).ne'
    (Real.rpow_pos_of_pos hln _).ne']
  rw [Real.log_rpow hn0, Real.log_rpow hln, Real.log_exp]
  ring

theorem log_scale_with_power (n θ τ p : ℝ) (hn : 1 < n) :
    Real.log (subcriticalScale n θ τ * (Real.log n) ^ p) =
      -θ * Real.log n - kappa θ τ * Real.sqrt (Real.log n) +
        (θ / 2 + p) * Real.log (Real.log n) := by
  rw [Real.log_mul (scale_pos n θ τ hn).ne'
    (Real.rpow_pos_of_pos (Real.log_pos hn) p).ne',
    log_scale n θ τ hn, Real.log_rpow (Real.log_pos hn)]
  ring

/-- Logs of the risk bracket, conditional only on the two actual numerical bounds. -/
theorem log_bracket (n θ τ ν c C R : ℝ) (hn : 1 < n)
    (hc : 0 < c) (hC : 0 < C)
    (hl : c * subcriticalScale n θ τ * Real.log n ≤ R)
    (hu : R ≤ C * subcriticalScale n θ τ * (Real.log n) ^ (ν / 2 + 1 / 4)) :
    Real.log c - θ * Real.log n - kappa θ τ * Real.sqrt (Real.log n) +
      (θ / 2 + 1) * Real.log (Real.log n) ≤ Real.log R ∧
    Real.log R ≤ Real.log C - θ * Real.log n -
      kappa θ τ * Real.sqrt (Real.log n) +
        (θ / 2 + ν / 2 + 1 / 4) * Real.log (Real.log n) := by
  have hln := Real.log_pos hn
  have hs := scale_pos n θ τ hn
  have hl0 : 0 < c * subcriticalScale n θ τ * Real.log n := mul_pos (mul_pos hc hs) hln
  have hR : 0 < R := lt_of_lt_of_le hl0 hl
  constructor
  · have h := Real.log_le_log hl0 hl
    rw [Real.log_mul (mul_pos hc hs).ne' hln.ne',
      Real.log_mul hc.ne' hs.ne', log_scale n θ τ hn] at h
    linarith
  · have h := Real.log_le_log hR hu
    rw [Real.log_mul (mul_pos hC hs).ne'
      (Real.rpow_pos_of_pos hln _).ne', Real.log_mul hC.ne' hs.ne',
      log_scale n θ τ hn, Real.log_rpow hln] at h
    linarith

end RoughRegime.Rates
