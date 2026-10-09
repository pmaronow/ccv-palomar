module

public import NearlyMinimax.PaperDegreeGuards
public import NearlyMinimax.PilotSeriesEnvelope
public import NearlyMinimax.ActualVarianceAllocation


@[expose] public section

/-! The genuine factorial-pilot envelope is bounded by the scalar allocation.
Every degree and sample-denominator guard follows from the actual paper profile. -/
noncomputable section
open Filter
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def paperPilotMomentFactor {d : ℕ} (C : ModelConstants d) (A : ℝ) : ℝ :=
  A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
    preconditionedPilotMomentConstant C C.order)

theorem paperPilotMomentFactor_nonneg {d : ℕ} (C : ModelConstants d) (A : ℝ) :
    0 ≤ paperPilotMomentFactor C A := by
  unfold paperPilotMomentFactor
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)

theorem dyadicPilotSeries_eq_factorialSeries {d : ℕ} (C : ModelConstants d)
    (A Λ : ℝ) (j m : ℕ) :
    dyadicPilotSeries C A Λ j m = factorialSeries (m + anchoredDimension d C.order + 1)
      (paperPilotMomentFactor C A * dyadicPilotScale d j / Λ) := by
  unfold dyadicPilotSeries factorialSeries paperPilotMomentFactor
  simpa only [mul_assoc] using (Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    ((k + 1).factorial : ℝ) *
      (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
        preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (k + 1))
    (m + anchoredDimension d C.order + 1))

theorem factorialSeries_mono_argument (D : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    factorialSeries D x ≤ factorialSeries D y := by
  unfold factorialSeries
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (Nat.cast_nonneg _)

/-- A genuine pilot block denominator and a fixed model constant dominate the
actual raw-feature moment argument. -/
theorem paper_pilot_series_argument_le {d : ℕ} (C : ModelConstants d) (A : ℝ)
    {n Λ C₀ : ℝ} (hn : 0 < n) (hΛ : n / 12 ≤ Λ)
    (hC : 12 * paperPilotMomentFactor C A ≤ C₀) (j : ℕ) :
    paperPilotMomentFactor C A * dyadicPilotScale d j / Λ ≤ C₀ * dyadicPilotScale d j / n := by
  have hp := paperPilotMomentFactor_nonneg C A
  have hk := (dyadicPilotScale_pos d j).le
  have hΛpos : 0 < Λ := (div_pos hn (by norm_num)).trans_le hΛ
  have hCpos : 0 ≤ C₀ := (mul_nonneg (by norm_num) hp).trans hC
  apply (div_le_div_iff₀ hΛpos hn).mpr
  have hm := mul_le_mul_of_nonneg_right hC hk
  have hnΛ := mul_le_mul_of_nonneg_left hΛ (mul_nonneg hCpos hk)
  nlinarith

/-- Exact total degree and original normalization give a levelwise domination
by the already-proved scalar variance profile. -/
theorem paper_pilot_series_weight_le_profile {d : ℕ} (C : ModelConstants d) (A a offset : ℝ)
    {n Λ C₀ C_D : ℝ} (hn : 0 < n) (hΛ : n / 12 ≤ Λ) (hΛn : Λ ≤ n)
    (hC : 0 < C₀) (hD : 0 < C_D) (hS : 0 < allocationWidth a offset n)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) (j : ℕ)
    (hdegree : paperDyadicTotalDegree C a offset (C₀ * C_D) n j =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j))) :
    dyadicPilotSeries C A Λ j (paperDyadicApproximationDegree C a offset (C₀ * C_D) n j) *
        max 1 (Λ / dyadicPilotScale d j) ≤
      profileVarianceWeight C₀ C_D (paperDegreeSlope C) (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j) := by
  rw [actual_profileVarianceWeight_eq_cell_weight j hC hD hn hS, ← dyadicPilotScale_eq_exp C]
  rw [dyadicPilotSeries_eq_factorialSeries]
  have hΛpos : 0 < Λ := (div_pos hn (by norm_num)).trans_le hΛ
  have hx : 0 ≤ paperPilotMomentFactor C A * dyadicPilotScale d j / Λ :=
    div_nonneg (mul_nonneg (paperPilotMomentFactor_nonneg C A) (dyadicPilotScale_pos _ _).le) hΛpos.le
  have hseries := factorialSeries_mono_argument
    (paperDyadicTotalDegree C a offset (C₀ * C_D) n j) hx
    (paper_pilot_series_argument_le C A hn hΛ hcoef j)
  rw [hdegree] at hseries
  change factorialSeries (paperDyadicTotalDegree C a offset (C₀ * C_D) n j) _ * _ ≤ _
  rw [hdegree]
  exact mul_le_mul hseries (max_le_max le_rfl (div_le_div_of_nonneg_right hΛn (dyadicPilotScale_pos _ _).le))
    (by positivity) (factorialSeries_nonneg _
      (div_nonneg (mul_nonneg hC.le (dyadicPilotScale_pos _ _).le) hn.le))

/-- Uniform comparison of the actual maximum series on the actual three-block
pilot sample with the scalar maximum at H=C₀ C_D. -/
theorem eventually_paper_dyadic_series_envelope_le {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (A a offset C₀ C_D : ℝ)
    (ha : 0 < a) (hC : 0 < C₀) (hD : 0 < C_D)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) :
    ∀ᶠ n : ℕ in atTop,
      dyadicSeriesEnvelope C A ((threeBlockSize n : ℝ) / 2)
        (paperDyadicTerminalLevel C a offset (C₀ * C_D) n)
        (paperDyadicApproximationDegree C a offset (C₀ * C_D) n) ≤
      actualVarianceMaximum (paperDyadicStep C) a offset C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) n := by
  have hdegree : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      paperDyadicTotalDegree C a offset (C₀ * C_D) n j =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j)) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_paper_total_degree_eq_floor C hs a offset (C₀ * C_D) ha)
  have hwidth : ∀ᶠ n : ℕ in atTop, 0 < allocationWidth a offset n :=
    tendsto_natCast_atTop_atTop.eventually
      ((allocationWidth_tendsto_atTop ha offset).eventually (eventually_gt_atTop (0 : ℝ)))
  filter_upwards [hdegree, hwidth, eventually_ge_atTop (6 : ℕ)] with n hd hS h6
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hΛ : (n : ℝ) / 12 ≤ (threeBlockSize n : ℝ) / 2 := by linarith [threeBlockSize_fraction h6]
  have hΛn : (threeBlockSize n : ℝ) / 2 ≤ n := by
    have hm : threeBlockSize n ≤ n := by unfold threeBlockSize; omega
    have hmR : (threeBlockSize n : ℝ) ≤ n := by exact_mod_cast hm
    linarith [Nat.cast_nonneg (α := ℝ) (threeBlockSize n)]
  unfold dyadicSeriesEnvelope
  apply Finset.sup'_le
  intro j _
  apply (paper_pilot_series_weight_le_profile C A a offset hn hΛ hΛn hC hD hS hcoef j.val (hd j.val)).trans
  unfold actualVarianceMaximum
  exact Finset.le_sup' (s := Finset.range
    (terminalAllocationLevel (paperDyadicStep C) a offset (C₀ * C_D) (paperDegreeReserve C) n + 1))
    (b := j.val) (fun i : ℕ => profileVarianceWeight C₀ C_D (paperDegreeSlope C) (allocationWidth a offset n)
      (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n i)) (Finset.mem_range.mpr j.isLt)

/-- Consequently the true statistical factorial envelope has the explicit
fine-level bound at the paper allocation, without a variance-budget premise. -/
theorem eventually_paper_dyadic_series_envelope_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (A a offset C₀ C_D : ℝ)
    (ha : 0 < a) (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
    (hDβ : 4 * paperDegreeSlope C ≤ C_D)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) :
    ∀ᶠ n : ℕ in atTop,
      dyadicSeriesEnvelope C A ((threeBlockSize n : ℝ) / 2)
        (paperDyadicTerminalLevel C a offset (C₀ * C_D) n)
        (paperDyadicApproximationDegree C a offset (C₀ * C_D) n) ≤
      2 * C₀ * C_D ^ 2 * (allocationWidth a offset n) ^ 2 *
        Real.exp (paperDegreeSlope C * (allocationWidth a offset n) ^ 2 / 4) := by
  have hβ : 0 ≤ paperDegreeSlope C := (div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)).le
  have hγ : 0 ≤ paperDegreeReserve C := by
    unfold paperDegreeReserve
    exact div_nonneg (by positivity) (paperSpatialExponent_pos C hs).le
  have hb : ∀ᶠ n : ℕ in atTop,
      actualVarianceMaximum (paperDyadicStep C) a offset C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) n ≤
      2 * C₀ * C_D ^ 2 * (allocationWidth a offset n) ^ 2 *
        Real.exp (paperDegreeSlope C * (allocationWidth a offset n) ^ 2 / 4) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_actualVarianceMaximum_bound (paperDyadicStep_pos C) ha hC hD hDβ hβ hγ offset)
  filter_upwards [eventually_paper_dyadic_series_envelope_le C hs A a offset C₀ C_D ha
    (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD) hcoef, hb] with n hn hb
  exact hn.trans hb

end NearlyMinimax
