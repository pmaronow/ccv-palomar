module

public import NearlyMinimax.UpperAllocationParameters
public import NearlyMinimax.DyadicSpatialRounding


@[expose] public section

/-! The paper's actual terminal depth, finest dyadic grid and spatial risk scale. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def paperAllocatedDepth {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  roundedTerminalDepth (paperDyadicStep C) (Real.log x)
    (candidateTerminalDepth (paperUpperSaddle C) (paperUpperShift C) H (paperDegreeReserve C) x)

def paperAllocatedLogSide {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  spatialBalanceLog C.smoothness d (Real.log x) (paperAllocatedDepth C H x)

def paperAllocatedFinestLevel {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℕ :=
  dyadicLevelFromLogSide (paperAllocatedLogSide C H x)

def paperAllocatedSide {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  dyadicRoundedSide (paperAllocatedLogSide C H x)

def paperAllocatedRiskScale {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  Real.exp (-rateExponent C.smoothness d * Real.log x -
    paperUpperRiskDepthCoefficient C * paperAllocatedDepth C H x)

theorem paperAllocatedDepth_eq_level {d : ℕ} (C : ModelConstants d) (H x : ℝ) :
    paperAllocatedDepth C H x = paperDyadicStep C *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) - Real.log x := rfl

theorem eventually_paper_allocated_depth_le_width {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∀ᶠ x : ℝ in atTop, paperAllocatedDepth C H x ≤
      allocationWidth (paperUpperSaddle C) (paperUpperShift C) x := by
  have hw := allocationWidth_tendsto_atTop (paperUpperSaddle_pos C hreg) (paperUpperShift C)
  filter_upwards [hw.eventually (eventually_ge_atTop (2 : ℝ)),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_terminal_cell_log_nonneg (paperUpperSaddle_pos C hreg) hH
      (paperUpperShift C) (paperDegreeReserve C)] with x hS hHS hLT
  have ht := (roundedTerminalDepth_bounds (paperDyadicStep_pos C) hLT).2
  have hlog : 0 ≤ Real.log (allocationWidth (paperUpperSaddle C) (paperUpperShift C) x) :=
    Real.log_nonneg (by linarith only [hS])
  have hlogH : 0 ≤ Real.log (H * allocationWidth (paperUpperSaddle C) (paperUpperShift C) x) :=
    Real.log_nonneg hHS
  have hm := mul_nonneg (paperDegreeReserve_pos C hreg.1).le hlog
  unfold candidateTerminalDepth at ht
  exact ht.trans (by linarith only [hlogH, hm])

/-- The actual finest pair grid refines the allocated terminal pilot grid. -/
theorem eventually_paper_allocated_grid_guard {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∀ᶠ x : ℝ in atTop,
      paperAllocatedLogSide C H x ≤ 0 ∧
      paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x ≤
        paperAllocatedFinestLevel C H x := by
  have hw := allocationWidth_tendsto_atTop (paperUpperSaddle_pos C hreg) (paperUpperShift C)
  filter_upwards [hw.eventually (eventually_ge_atTop (2 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_paper_allocated_depth_le_width C hreg hH] with x hS hL hT
  have hb := quadratic_allocation_budget (paperDegreeSlope_pos C hreg.1)
    (show 0 ≤ paperUpperEta C + 2 by linarith only [paperUpperEta_pos C])
    (show 0 ≤ allocationWidth (paperUpperSaddle C) (paperUpperShift C) x by linarith only [hS])
    (show allocationWidth (paperUpperSaddle C) (paperUpperShift C) x =
      paperUpperSaddle C * Real.sqrt (Real.log x) -
        (1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C) by rfl)
  have hbase : paperDegreeSlope C * (paperUpperSaddle C * Real.sqrt (Real.log x)) ^ 2 / 4 =
      2 * paperUpperVarpi C * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hL]
    calc
      _ = (paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4) * Real.log x := by ring
      _ = _ := by rw [paper_upper_saddle_budget_identity C hreg]
  rw [hbase] at hb
  have hm := mul_le_mul_of_nonneg_left hT (paperUpperEta_pos C).le
  have hquad : 0 ≤ paperDegreeSlope C *
      (allocationWidth (paperUpperSaddle C) (paperUpperShift C) x) ^ 2 / 4 := by
    exact div_nonneg (mul_nonneg (paperDegreeSlope_pos C hreg.1).le (sq_nonneg _)) (by norm_num)
  have hn : -2 * paperUpperVarpi C * Real.log x +
      paperUpperEta C * paperAllocatedDepth C H x ≤ 0 := by
    nlinarith only [hb, hm, hquad, hS]
  rw [← paper_spatial_reserve_identity C hreg] at hn
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  have hlevel : Real.log x + paperAllocatedDepth C H x =
      paperDyadicStep C * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) := by
    rw [paperAllocatedDepth_eq_level]
    ring
  rw [hlevel] at hn
  have hlog : 2 / (d : ℝ) * (paperDyadicStep C *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ)) =
      2 * (Real.log 2 * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ)) := by
    unfold paperDyadicStep
    field_simp
  rw [hlog] at hn
  have hg : paperAllocatedLogSide C H x + Real.log 2 *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) ≤ 0 := by
    change spatialBalanceLog C.smoothness d (Real.log x) (paperAllocatedDepth C H x) + _ ≤ 0
    linarith only [hn]
  have hnonneg : 0 ≤ Real.log 2 *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) :=
    mul_nonneg (Real.log_pos (by norm_num)).le (Nat.cast_nonneg _)
  exact ⟨by linarith only [hg, hnonneg], dyadicRoundedLevel_ge hg⟩

theorem paper_allocated_pair_noise_bound {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (H x : ℝ) (hg : paperAllocatedLogSide C H x ≤ 0) :
    Real.exp (-Real.log x - (d : ℝ) / 2 * dyadicRoundedLogSide (paperAllocatedLogSide C H x)) ≤
      Real.exp ((d : ℝ) / 2 * Real.log 2) * paperAllocatedRiskScale C H x := by
  have h := dyadicRounded_noise_bound hg (Nat.cast_nonneg d) (Real.log x)
  rw [paperAllocatedLogSide, spatial_balance_rate hreg.1 hreg.2] at h
  exact h

/-- The displayed stretched exponential and logarithmic gap are exact. -/
theorem paper_allocated_risk_scale_bracket {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ x : ℝ in atTop,
      A * Real.exp (-rateExponent C.smoothness d * Real.log x -
        stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log x) +
        (lowerLogPower C.smoothness d + paperLogGap C) * Real.log (Real.log x)) ≤
          paperAllocatedRiskScale C H x ∧
      paperAllocatedRiskScale C H x ≤ B * Real.exp (-rateExponent C.smoothness d * Real.log x -
        stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log x) +
        (lowerLogPower C.smoothness d + paperLogGap C) * Real.log (Real.log x)) := by
  obtain ⟨A, B, hA, hB, hb⟩ := rounded_upper_saddle_scale_bracket
    (paperUpperSaddle_pos C hreg) hH (paperDyadicStep_pos C)
    (paperUpperShift C) (paperDegreeReserve C) (rateExponent C.smoothness d)
    (paperUpperRiskDepthCoefficient_pos C hreg.1).le
  refine ⟨A, B, hA, hB, ?_⟩
  simpa only [paperAllocatedRiskScale, paperAllocatedDepth, ← mul_assoc,
    paper_upper_stretch_identity C hreg, paper_upper_log_power_identity C hreg.1] using hb

end NearlyMinimax
