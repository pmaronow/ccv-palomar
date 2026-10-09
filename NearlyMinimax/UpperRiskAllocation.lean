module

public import NearlyMinimax.UpperSpatialAllocation


@[expose] public section

/-! Bias and sample noise at the original allocated and rounded bandwidth. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def paperUpperRootReserve {d : ℕ} (C : ModelConstants d) : ℝ :=
  ((d : ℝ) - 4 * C.smoothness) / (4 * ((d : ℝ) + 4))

theorem paperUpperRootReserve_pos {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) : 0 < paperUpperRootReserve C := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  exact div_pos (sub_pos.mpr hreg.2) (mul_pos (by norm_num) (by positivity))

theorem eventually_paper_allocated_root_noise_bound {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-Real.log x / 2) ≤
      Real.exp (-paperUpperRootReserve C * Real.log x) * paperAllocatedRiskScale C H x := by
  have hlim := tendsto_sqrt_log_div_log.const_mul
    (paperUpperRiskDepthCoefficient C * paperUpperSaddle C)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds (paperUpperRootReserve_pos C hreg)),
    eventually_paper_allocated_depth_le_width C hreg hH,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hT hL
  have hchi := paperUpperRiskDepthCoefficient_pos C hreg.1
  have hbeta := paperDegreeSlope_pos C hreg.1
  have hshift : 0 ≤ paperUpperShift C := by
    unfold paperUpperShift
    exact add_nonneg (by norm_num) (div_nonneg
      (mul_nonneg (by norm_num) (by linarith only [paperUpperEta_pos C])) hbeta.le)
  have hS : allocationWidth (paperUpperSaddle C) (paperUpperShift C) x ≤
      paperUpperSaddle C * Real.sqrt (Real.log x) := by
    unfold allocationWidth
    linarith only [hshift]
  have hm := mul_le_mul_of_nonneg_left (hT.trans hS) hchi.le
  have hsmall : paperUpperRiskDepthCoefficient C * paperUpperSaddle C * Real.sqrt (Real.log x) ≤
      paperUpperRootReserve C * Real.log x := by
    rw [← mul_div_assoc] at hx
    exact ((div_lt_iff₀ hL).mp hx).le
  have hgap : 1 / 2 - rateExponent C.smoothness d = 2 * paperUpperRootReserve C := by
    rw [half_minus_rateExponent hreg.1 hreg.2]
    unfold paperUpperRootReserve
    have hd4 : (d : ℝ) + 4 ≠ 0 := by positivity
    field_simp
    ring
  have hgapL := congrArg (fun t : ℝ => t * Real.log x) hgap
  unfold paperAllocatedRiskScale
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hm, hsmall, hgapL]

/-- The true rounded bias squared is controlled by the common scalar risk. -/
theorem paper_allocated_bias_square_bound {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (H x : ℝ) (hg : paperAllocatedLogSide C H x ≤ 0) :
    (paperAllocatedSide C H x *
      (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x)) ^
        (-paperSpatialExponent C)) ^ 2 ≤ paperAllocatedRiskScale C H x := by
  have hs := (dyadicRoundedSide_bounds hg).2
  have hs0 : 0 ≤ paperAllocatedSide C H x := (Real.exp_pos _).le
  have hpow := pow_le_pow_left₀ hs0 hs 2
  rw [mul_pow]
  have hK : 0 < dyadicPilotScale d
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x) := dyadicPilotScale_pos _ _
  apply (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)).trans_eq
  rw [dyadicPilotScale_eq_exp C, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  unfold paperAllocatedRiskScale
  congr 1
  have hdepth : Real.log x + paperAllocatedDepth C H x = paperDyadicStep C *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) := by
    rw [paperAllocatedDepth_eq_level]
    ring
  have hbalance := spatial_balance hreg.1 hreg.2 (Real.log x) (paperAllocatedDepth C H x)
  have hrate := spatial_balance_rate hreg.1 hreg.2 (Real.log x) (paperAllocatedDepth C H x)
  change _ = -rateExponent C.smoothness d * Real.log x -
    2 * (C.smoothness - 1) / ((d : ℝ) + 4) * paperAllocatedDepth C H x
  unfold paperAllocatedLogSide paperSpatialExponent
  rw [hdepth] at hbalance
  nlinarith only [hbalance, hrate]

end NearlyMinimax
