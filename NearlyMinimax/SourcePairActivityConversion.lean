module

public import NearlyMinimax.FinePairRowActivity


@[expose] public section

/-! Actual source-scale absorption of the unit/coarse/fine pair caps.
No degree-dependent exponential is added to the local activity. -/
noncomputable section
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem source_pair_unit_scale_le {D N tau c0 : ℝ} (hD : 0 ≤ D)
    (hc0 : 0 ≤ c0) (htau : tau ≤ c0) (hN : D*Real.exp (c0*D) ≤ N) :
    D^2*Real.exp (tau*D) ≤ N^2 := by
  have h0 : 0 ≤ D*Real.exp (c0*D) := by positivity
  have hs := pow_le_pow_left₀ h0 hN 2
  rw [mul_pow, ← Real.exp_nat_mul] at hs
  have he : Real.exp (tau*D) ≤ Real.exp ((2:ℝ)*(c0*D)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg D)).trans hs

theorem source_pair_polynomial_exponential_le {D : ℝ} (hD : 0 ≤ D) :
    D^2*Real.exp (-D) ≤ 2 := by
  have hp := Real.pow_div_factorial_le_exp D hD 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one] at hp
  have hs : D^2 ≤ 2*Real.exp D := by linarith
  have h := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-D)).le
  have he : Real.exp D * Real.exp (-D) = 1 := by rw [← Real.exp_add]; simp
  calc _ ≤ 2*Real.exp D*Real.exp (-D) := h
       _ = 2 := by rw [mul_assoc,he,mul_one]

/-- The actual common cutoff cancels both scale powers and one exterior exponent. -/
theorem source_pair_coarse_scale_le {D N tau c0 : ℝ} (hD : 0 ≤ D)
    (hc0 : 1 ≤ c0) (htau : tau ≤ c0) :
    D^2*Real.exp (tau*D)*(N*Real.exp (-c0*D))^2 ≤ 2*N^2 := by
  have he : Real.exp ((tau-2*c0)*D) ≤ Real.exp (-D) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hp := source_pair_polynomial_exponential_le hD
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg D)
  have hbound : D^2*Real.exp ((tau-2*c0)*D) ≤ 2 := hm.trans hp
  have hid : D^2*Real.exp (tau*D)*(N*Real.exp (-c0*D))^2 =
      N^2*(D^2*Real.exp ((tau-2*c0)*D)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show (tau-2*c0)*D = tau*D+((2:ℕ):ℝ)*(-c0*D) by norm_num; ring, Real.exp_add]
    ring
  rw [hid]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (sq_nonneg N)

/-- Pure scalar aggregation for the actual three pair caps. The cap
coefficients are the frozen finite signed-row variation bounds. -/
theorem source_pair_total_activity_le {d D N tau c0 B Rsp EM unit coarse fine : ℝ}
    (hd : 0 ≤ d) (hD : 0 ≤ D) (hc0 : 1 ≤ c0) (htau : tau ≤ c0)
    (hN : D*Real.exp (c0*D) ≤ N) (hRsp : 0 ≤ Rsp) (hEM : 1 ≤ EM)
    (hunit : unit ≤ B^2*D^2*Real.exp (tau*D)*Rsp)
    (hcoarse : coarse ≤ 128*d*B^2*D^2*Real.exp (tau*D)*Rsp*(N*Real.exp (-c0*D))^2)
    (hfine : fine ≤ 256*d*B^2*EM*Rsp*N^2) :
    unit+coarse+fine ≤ B^2*Rsp*(1+512*d)*N^2*EM := by
  have hu := source_pair_unit_scale_le hD (by linarith) htau hN
  have hc := source_pair_coarse_scale_le (N := N) hD hc0 htau
  have hu' : unit ≤ B^2*Rsp*N^2 := by
    have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ B^2*Rsp by positivity)
    apply hunit.trans
    convert h using 1 <;> ring
  have hc' : coarse ≤ 256*d*B^2*Rsp*N^2 := by
    have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 128*d*B^2*Rsp by positivity)
    apply hcoarse.trans
    convert h using 1 <;> ring
  have hU := mul_le_mul_of_nonneg_left hEM (show 0 ≤ B^2*Rsp*N^2 by positivity)
  have hC := mul_le_mul_of_nonneg_left hEM (show 0 ≤ 256*d*B^2*Rsp*N^2 by positivity)
  nlinarith only [hu',hc',hfine,hU,hC]

end NearlyMinimax
