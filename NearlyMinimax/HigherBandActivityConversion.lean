module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.LowerActivityHierarchy


@[expose] public section

/-! Fixed geometric-ratio conversion of the genuine higher-band activation
caps. Density and interpolation constants are chosen before the degree and
sample size; no final activity estimate is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def higherBandInterpolationBase (d : ℕ) (lam : ℝ) : ℝ := 1024 * |lam| *(d : ℝ)^2

def higherBandGeometricConstant (B Ci : ℝ) : ℝ := 2*(1+B)*(1+Ci)
def higherBandGeometricPrefactor (B Ci Rsp : ℝ) : ℝ := 8*Rsp*(1+B)^2*(1+Ci)
def higherBandGeometricRatio (d D : ℕ) (Cact H base a : ℝ) : ℝ :=
  Cact*(D : ℝ)*H*base^(a/(d : ℝ))

theorem higher_band_coefficient_absorption {r : ℕ} (hr : 2 ≤ r) {b B Ci : ℝ}
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hCi : 0 ≤ Ci) (hbB : b ≤ B) :
    b^r * Ci^(r-1) * (2*(r : ℝ)) ≤
      (8*(1+B)^2*(1+Ci)) * (higherBandGeometricConstant B Ci)^(r-2) := by
  have hrEq : r = (r-2)+2 := by omega
  have hrEq1 : r-1 = (r-2)+1 := by omega
  have hbpow : b^r ≤ (1+B)^2*(1+B)^(r-2) := by
    calc b^r ≤ (1+B)^r := pow_le_pow_left₀ hb (by linarith) r
         _ = _ := by nth_rw 1 [hrEq]; rw [pow_add]; ring
  have hcipow : Ci^(r-1) ≤ (1+Ci)*(1+Ci)^(r-2) := by
    calc Ci^(r-1) ≤ (1+Ci)^(r-1) := pow_le_pow_left₀ hCi (by linarith) _
         _ = _ := by rw [hrEq1, pow_succ]; ring
  have hrpow : (r : ℝ) ≤ (2 : ℝ)^r := by exact_mod_cast (show r < 2^r from Nat.lt_two_pow_self).le
  have hrcoef : 2*(r : ℝ) ≤ 8*(2 : ℝ)^(r-2) := by
    have he : (2 : ℝ)^r = 4*(2 : ℝ)^(r-2) := by rw [hrEq, pow_add]; norm_num; ring
    rw [he] at hrpow
    nlinarith
  have h := mul_le_mul (mul_le_mul hbpow hcipow (by positivity) (by positivity)) hrcoef
    (by positivity) (by positivity)
  apply h.trans_eq
  unfold higherBandGeometricConstant
  rw [mul_pow, mul_pow]
  ring

/-- Exact source target-power identities, with natural r-2 and real dimension division. -/
theorem higherBandTargetScale_power {d r : ℕ} (_hr : 2 ≤ r) {base : ℝ}
    (hbase : 0 ≤ base) (a : ℝ) :
    (base^((a/(d : ℝ))*(r-2 : ℕ))) = (base^(a/(d : ℝ)))^(r-2) :=
  Real.rpow_mul_natCast hbase _ _

theorem higherBandTargetScale_eq {d r : ℕ} (hr : 2 ≤ r) (N mu : ℝ)
    (hbase : 0 ≤ mu*(1+Real.log N)) :
    higherBandTargetScale d r N mu =
      N*((mu*(1+Real.log N))^(1/(d : ℝ)))^(r-2) := by
  unfold higherBandTargetScale
  congr 1
  have he : ((r : ℝ)-2)/(d : ℝ) = (1/(d : ℝ))*(r-2 : ℕ) := by
    rw [Nat.cast_sub hr]
    push_cast
    ring
  rw [he, Real.rpow_mul_natCast hbase]

/-- A generic true cap is a geometric-ratio row bound once its T² and
logarithmic scale are bounded by the actual target powers. -/
theorem higherBandRowActivityCap_geometric_le {d r m D q : ℕ} (hr : 2 ≤ r)
    (a b C lam T B H base P alpha : ℝ) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hbase : 0 ≤ base) (hP : 0 ≤ P) (_hH : 0 ≤ H)
    (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hlog : 1+Real.log T ≤ H)
    (hT2 : T^2 ≤ P*(base^(alpha/(d : ℝ)))^(r-2)) :
    higherBandRowActivityCap d r m D q a b C lam T ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) *
      (D : ℝ)^2 * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) * P *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) H base alpha)^(r-2) := by
  have hb0 : 0 ≤ ordinaryDensityActivityBase a b := by unfold ordinaryDensityActivityBase; positivity
  have hCi : 0 ≤ higherBandInterpolationBase d lam := by unfold higherBandInterpolationBase; positivity
  have hcoef := higher_band_coefficient_absorption hr hb0 hB hCi hbB
  have hlog0 : 0 ≤ 1+Real.log T := by linarith [Real.log_nonneg hT]
  have hlogpow := pow_le_pow_left₀ hlog0 hlog (r-2)
  have hCact : 0 ≤ higherBandGeometricConstant B (higherBandInterpolationBase d lam) := by
    unfold higherBandGeometricConstant
    positivity
  have hDpower : (D : ℝ)^r = (D : ℝ)^2*(D : ℝ)^(r-2) := by
    nth_rw 1 [show r=(r-2)+2 by omega]
    rw [pow_add]
    ring
  have hscale := mul_le_mul hT2 hlogpow (by positivity) (by positivity)
  have h := mul_le_mul hcoef hscale (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (D : ℝ)^r * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) *
      ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) by positivity)
  convert hh using 1 <;>
    simp only [higherBandRowActivityCap, higherBandInterpolationCap, higherBandGeometricPrefactor,
      higherBandGeometricRatio, higherBandInterpolationBase, hDpower, mul_pow] <;> ring

theorem higherBandTargetScale_le_N {d r : ℕ} (_hd : 0 < d) (hr : 2 ≤ r)
    {N mu : ℝ} (hN : 1 ≤ N) (hmu : 0 ≤ mu) (hbase1 : mu*(1+Real.log N) ≤ 1) :
    higherBandTargetScale d r N mu ≤ N := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  have hpower := Real.rpow_le_one hbase hbase1
    (show 0 ≤ ((r : ℝ)-2)/(d : ℝ) by
      have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
      exact div_nonneg (sub_nonneg.mpr hrR) (Nat.cast_nonneg _))
  unfold higherBandTargetScale
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower (by linarith : 0 ≤ N)

/-- Actual coarse target cap, uniformly for every legal selected target. -/
theorem higherBandRowActivityCap_coarse_geometric_le {d r D q : ℕ} (hd : 0 < d) (hr : 2 ≤ r)
    (a b C lam N mu ell B : ℝ) (hN : 1 ≤ N) (hmu : 0 ≤ mu)
    (hbase1 : mu*(1+Real.log N) ≤ 1)
    (hT : 1 ≤ min ell (higherBandTargetScale d r N mu)) (hB : 0 ≤ B)
    (hbB : ordinaryDensityActivityBase a b ≤ B) :
    higherBandRowActivityCap d r D D q a b C lam (min ell (higherBandTargetScale d r N mu)) ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) *
      (D : ℝ)^2 * Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) * (N*ell) *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (mu*(1+Real.log N)) 1)^(r-2) := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  have hell : 0 ≤ ell := by linarith [min_le_left ell (higherBandTargetScale d r N mu)]
  have hnu := higherBandTargetScale_le_N hd hr hN hmu hbase1
  have hTN : min ell (higherBandTargetScale d r N mu) ≤ N := (min_le_right _ _).trans hnu
  apply higherBandRowActivityCap_geometric_le hr a b C lam _ B _ _ (N*ell) 1 hT hB hbase (by positivity) hH hbB
  · exact add_le_add_right (Real.log_le_log (by linarith : 0 < min ell (higherBandTargetScale d r N mu)) hTN) 1
  · have ht0 : 0 ≤ min ell (higherBandTargetScale d r N mu) := by linarith
    have h := mul_le_mul (min_le_left ell (higherBandTargetScale d r N mu))
      (min_le_right ell (higherBandTargetScale d r N mu)) ht0 hell
    calc
      _ ≤ ell * higherBandTargetScale d r N mu := by simpa only [pow_two] using h
      _ = _ := by rw [higherBandTargetScale_eq hr N mu hbase]; ring

/-- Actual fine target cap with the exact q2 power, uniformly over all legal selected targets. -/
theorem higherBandRowActivityCap_fine_geometric_le {d r M D q : ℕ} (hd : 0 < d) (hr : 2 ≤ r)
    (a b C lam N mu B : ℝ) (hN : 1 ≤ N) (hmu : 0 ≤ mu)
    (hbase1 : mu*(1+Real.log N) ≤ 1) (hT : 1 ≤ higherBandTargetScale d r N mu)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B) :
    higherBandRowActivityCap d r M D q a b C lam (higherBandTargetScale d r N mu) ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) *
      (D : ℝ)^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) * N^2 *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (mu*(1+Real.log N)) 2)^(r-2) := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  have hnu := higherBandTargetScale_le_N hd hr hN hmu hbase1
  apply higherBandRowActivityCap_geometric_le hr a b C lam _ B _ _ (N^2) 2 hT hB hbase (by positivity) hH hbB
  · exact add_le_add_right (Real.log_le_log (by linarith : 0 < higherBandTargetScale d r N mu) hnu) 1
  · apply le_of_eq
    rw [higherBandTargetScale_eq hr N mu hbase, mul_pow]
    have he : ((mu*(1+Real.log N))^(1/(d : ℝ)))^2 = (mu*(1+Real.log N))^(2/(d : ℝ)) := by
      rw [← Real.rpow_mul_natCast hbase]
      congr 1
      push_cast
      ring
    rw [← pow_mul, Nat.mul_comm (r-2) 2, pow_mul, he]

/-- Exact elementary density-base simplification, including the true exterior interval exponent. -/
theorem ordinaryDensityActivityBase_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ordinaryDensityActivityBase a b = Real.exp (1+densityIntervalExponent a b)*((b-a)/a) := by
  have he : b/densityMargin a b 0 = -((b-a)/a) := by
    unfold densityMargin
    field_simp [ha.ne', (ha.trans hab).ne', (sub_pos.mpr hab).ne']
    ring
  unfold ordinaryDensityActivityBase
  rw [he, abs_neg, abs_of_pos (div_pos (sub_pos.mpr hab) ha), exteriorTau_sqrt_ratio a b ha hab]
  rfl

def uniformOrdinaryDensityActivityBase (a b c0 : ℝ) : ℝ :=
  Real.exp (1+c0)*((b-a)/a)

/-- One fixed density base bounds every legal shrunk interval with tauM<=c0. -/
theorem ordinaryDensityActivityBase_shrunk_le {a b t c0 : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hshrink : a+t < b-t)
    (htau : densityIntervalExponent (a+t) (b-t) ≤ c0) :
    ordinaryDensityActivityBase (a+t) (b-t) ≤ uniformOrdinaryDensityActivityBase a b c0 := by
  have hab : a < b := by linarith
  have hap : 0 < a+t := by linarith
  rw [ordinaryDensityActivityBase_eq hap hshrink]
  have hratio : ((b-t)-(a+t))/(a+t) ≤ (b-a)/a := by
    apply (div_le_div_iff₀ hap ha).mpr
    nlinarith
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hratio
    (div_pos (sub_pos.mpr hshrink) hap).le (Real.exp_pos _).le

def higherBandSourceCact (d : ℕ) (a b c0 lam : ℝ) : ℝ :=
  higherBandGeometricConstant (uniformOrdinaryDensityActivityBase a b c0) (higherBandInterpolationBase d lam)

def higherBandSourceK (d q : ℕ) (a b c0 C lam : ℝ) : ℝ :=
  higherBandGeometricPrefactor (uniformOrdinaryDensityActivityBase a b c0) (higherBandInterpolationBase d lam)
    ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2))

theorem higherBandSourceCact_positive (d : ℕ) {a b c0 lam : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < higherBandSourceCact d a b c0 lam := by
  have hB : 0 < uniformOrdinaryDensityActivityBase a b c0 :=
    mul_pos (Real.exp_pos _) (div_pos (sub_pos.mpr hab) ha)
  unfold higherBandSourceCact higherBandGeometricConstant higherBandInterpolationBase
  positivity

theorem higherBandSourceK_nonneg (d q : ℕ) {a b c0 C lam : ℝ} (ha : 0 < a) (hab : a < b) :
    0 ≤ higherBandSourceK d q a b c0 C lam := by
  have hB : 0 < uniformOrdinaryDensityActivityBase a b c0 :=
    mul_pos (Real.exp_pos _) (div_pos (sub_pos.mpr hab) ha)
  unfold higherBandSourceK higherBandGeometricPrefactor higherBandInterpolationBase
  positivity

/-- Uniform actual shrunk-density coarse cap with fixed constants Cact and K. -/
theorem higherBandRowActivityCap_coarse_shrunk_geometric_le {d r M D q : ℕ}
    (hd : 0 < d) (hr : 2 ≤ r) (a b C lam N mu ell c0 : ℝ) (ha : 0 < a)
    (hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹) (htau : shrunkDensityExponent a b M ≤ c0)
    (hN : 1 ≤ N) (hmu : 0 ≤ mu) (hbase1 : mu*(1+Real.log N) ≤ 1)
    (hT : 1 ≤ min ell (higherBandTargetScale d r N mu)) :
    higherBandRowActivityCap d r D D q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam
      (min ell (higherBandTargetScale d r N mu)) ≤
      higherBandSourceK d q a b c0 C lam * (D : ℝ)^2 *
      Real.exp (shrunkDensityExponent a b M*(D : ℝ)) * (N*ell) *
      (higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
        (1+Real.log N) (mu*(1+Real.log N)) 1)^(r-2) := by
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hab : a < b := by linarith
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b c0 :=
    (mul_pos (Real.exp_pos _) (div_pos (sub_pos.mpr hab) ha)).le
  have hb := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have he : exteriorTau (((a+(M : ℝ)⁻¹)+(b-(M : ℝ)⁻¹))/((b-(M : ℝ)⁻¹)-(a+(M : ℝ)⁻¹))) =
      shrunkDensityExponent a b M := by
    rw [exteriorTau_sqrt_ratio _ _ (by linarith) hshrink]
    rfl
  have h := higherBandRowActivityCap_coarse_geometric_le (D := D) (q := q) hd hr
    (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam N mu ell _ hN hmu hbase1 hT hB hb
  simpa only [higherBandSourceK, higherBandSourceCact, he, mul_comm (D : ℝ) (shrunkDensityExponent a b M)] using h

/-- Uniform actual shrunk-density fine cap with the same fixed constants Cact and K. -/
theorem higherBandRowActivityCap_fine_shrunk_geometric_le {d r M D q : ℕ}
    (hd : 0 < d) (hr : 2 ≤ r) (a b C lam N mu c0 : ℝ) (ha : 0 < a)
    (hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹) (htau : shrunkDensityExponent a b M ≤ c0)
    (hN : 1 ≤ N) (hmu : 0 ≤ mu) (hbase1 : mu*(1+Real.log N) ≤ 1)
    (hT : 1 ≤ higherBandTargetScale d r N mu) :
    higherBandRowActivityCap d r M D q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam
      (higherBandTargetScale d r N mu) ≤
      higherBandSourceK d q a b c0 C lam * (D : ℝ)^2 *
      Real.exp (shrunkDensityExponent a b M*(M : ℝ)) * N^2 *
      (higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
        (1+Real.log N) (mu*(1+Real.log N)) 2)^(r-2) := by
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hab : a < b := by linarith
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b c0 :=
    (mul_pos (Real.exp_pos _) (div_pos (sub_pos.mpr hab) ha)).le
  have hb := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have he : exteriorTau (((a+(M : ℝ)⁻¹)+(b-(M : ℝ)⁻¹))/((b-(M : ℝ)⁻¹)-(a+(M : ℝ)⁻¹))) =
      shrunkDensityExponent a b M := by
    rw [exteriorTau_sqrt_ratio _ _ (by linarith) hshrink]
    rfl
  have h := higherBandRowActivityCap_fine_geometric_le (M := M) (D := D) (q := q) hd hr
    (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam N mu _ hN hmu hbase1 hT hB hb
  simpa only [higherBandSourceK, higherBandSourceCact, he, mul_comm (M : ℝ) (shrunkDensityExponent a b M)] using h

/-- The actual source geometric ratios agree exactly with the rounded
saddle hierarchy's q_a definitions. -/
theorem higherBandGeometricRatio_eq_lowerAliasQ (d : ℕ) (s m θ C Cact alpha x : ℝ) (τM : ℕ → ℝ) :
    higherBandGeometricRatio d (lowerSaddleD d m x) Cact (lowerAliasH s d m θ C τM x)
      (lowerSaddleMu d m θ C x*lowerAliasH s d m θ C τM x) alpha =
      lowerAliasQ s d m θ C Cact alpha τM x := rfl

end NearlyMinimax
