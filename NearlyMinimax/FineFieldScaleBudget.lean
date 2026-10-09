module

public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.FieldTailSummation


@[expose] public section

/-! The actual rounded saddle absorbs the higher-field scale energy into
mu² N^-d. The negative quadratic logarithmic scale is proved explicitly. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def lowerSaddleFineFieldScale (s d m theta C c0 : ℝ) (tauM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (2 * tauM (lowerSaddleM m x) * lowerSaddleM m x) *
    lowerSaddleN s d m theta C tauM x ^ (4 - d) *
    Real.exp (c0 * (2 * d - 4) * lowerSaddleD d m x)

theorem lowerSaddleFineFieldScale_positive (s d m theta C c0 : ℝ) (tauM : ℕ → ℝ) (x : ℝ) :
    0 < lowerSaddleFineFieldScale s d m theta C c0 tauM x := by
  unfold lowerSaddleFineFieldScale
  positivity [lowerSaddleN_positive s d m theta C tauM x]

theorem lowerSaddleFineFieldScale_tends_zero {s d m theta tau Ctau : ℝ}
    {tauM : ℕ → ℝ} (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (htheta : 0 < theta)
    (hcontrol : LowerExponentControl tauM tau Ctau) (C c0 : ℝ) :
    Tendsto (lowerSaddleFineFieldScale s d m theta C c0 tauM) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith only [hs, hd]
  have hd4 : 4 < d := by linarith only [hs, hd]
  have hM := lowerSaddleM_tendsto_atTop hm
  have hM2 : Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hM
  have htau := ((lowerSaddleTau_limit hm hcontrol).mul hM.inv_tendsto_atTop).const_mul 2
  have hN := (lowerSaddleLogN_div_M_sq_limit hd0 hm htheta hcontrol s C).const_mul (4 - d)
  have hD := (lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul (c0 * (2 * d - 4))
  have hh := (htau.add hN).add hD
  simp only [mul_zero, zero_add, add_zero] at hh
  apply positive_profile_tends_zero_of_log_div_negative
    (c := (4 - d) * (((d - 4 * s) / (d * (d + 4))) / m ^ 2)) hM2
    (by have hp : 0 < ((d - 4 * s) / (d * (d + 4))) / m ^ 2 := by positivity
        exact mul_neg_of_neg_of_pos (by linarith only [hd4]) hp)
    (Filter.Eventually.of_forall (lowerSaddleFineFieldScale_positive s d m theta C c0 tauM))
  refine hh.congr' ?_
  filter_upwards [hM.eventually (eventually_gt_atTop (0 : ℝ))] with x hMx
  unfold lowerSaddleFineFieldScale
  have hNp := lowerSaddleN_positive s d m theta C tauM x
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hNp _).ne',
    Real.log_exp, Real.log_exp, Real.log_rpow hNp]
  simp only [Pi.inv_apply]
  field_simp [hMx.ne']

theorem fine_field_scale_absorption {d N mu ell tau M D c0 : ℝ}
    (hN : 0 < N) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hell : ell = N * Real.exp (-c0 * D))
    (hscale : Real.exp (2 * tau * M) * N ^ (4 - d) *
      Real.exp (c0 * (2 * d - 4) * D) ≤ 1) :
    Real.exp (2 * tau * M) * mu ^ 4 * ell ^ (4 - 2 * d) ≤
      mu ^ 2 * N ^ (-d) := by
  have hNpow : N ^ (-d) * N ^ (4 - d) = N ^ (4 - 2 * d) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have he : Real.exp (-c0 * D) ^ (4 - 2 * d) = Real.exp (c0 * (2 * d - 4) * D) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hell, Real.mul_rpow hN.le (Real.exp_pos _).le, he]
  have hmu2 : mu ^ 2 ≤ 1 := pow_le_one₀ hmu hmu1
  have hprod : mu ^ 2 * (Real.exp (2 * tau * M) * N ^ (4 - d) *
      Real.exp (c0 * (2 * d - 4) * D)) ≤ 1 := by
    have h := mul_le_mul hmu2 hscale (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h
  calc
    _ = (mu ^ 2 * N ^ (-d)) * (mu ^ 2 *
        (Real.exp (2 * tau * M) * N ^ (4 - d) * Real.exp (c0 * (2 * d - 4) * D))) := by
      rw [show (mu ^ 2 * N ^ (-d)) * (mu ^ 2 *
          (Real.exp (2 * tau * M) * N ^ (4 - d) * Real.exp (c0 * (2 * d - 4) * D))) =
        mu ^ 4 * Real.exp (2 * tau * M) * (N ^ (-d) * N ^ (4 - d)) *
          Real.exp (c0 * (2 * d - 4) * D) by ring]
      rw [hNpow]
      ring
    _ ≤ (mu ^ 2 * N ^ (-d)) * 1 := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := mul_one _

theorem eventually_lowerSaddle_fine_field_energy_scale {s d m theta tau Ctau : ℝ}
    {tauM : ℕ → ℝ} (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (htheta : 0 < theta)
    (hcontrol : LowerExponentControl tauM tau Ctau) (C c0 : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (2 * tauM (lowerSaddleM m x) * lowerSaddleM m x) *
        lowerSaddleMu d m theta C x ^ 4 *
        lowerAliasCutoff s d m theta C c0 tauM x ^ (4 - 2 * d) ≤
          lowerSaddleMu d m theta C x ^ 2 * lowerSaddleN s d m theta C tauM x ^ (-d) := by
  have hd0 : 0 < d := by linarith only [hs, hd]
  filter_upwards [(lowerSaddleFineFieldScale_tends_zero hs hd hm htheta hcontrol C c0).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (lowerSaddleMu_tends_zero hd0 hm htheta C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with x hscale hmu hx
  apply fine_field_scale_absorption (lowerSaddleN_positive s d m theta C tauM x)
    (mul_nonneg hx.le (Real.rpow_pos_of_pos (lowerSaddleH_positive d m theta C x) _).le) hmu.le rfl
  exact hscale.le

end NearlyMinimax
