module

public import NearlyMinimax.DyadicBiasAllocation
public import NearlyMinimax.AnchoredCard
public import NearlyMinimax.SampleThirds
public import NearlyMinimax.DyadicPilotPointwise


@[expose] public section

/-! The actual floored degrees satisfy the factorial-lift sample guards.
The polynomial coordinate cost is the exact binomial feature dimension. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem paperPolynomialDimension_eq_anchoredDimension_add_one {d : ℕ} (C : ModelConstants d) :
    paperPolynomialDimension C = anchoredDimension d C.order + 1 := by
  unfold paperPolynomialDimension anchoredDimension
  rw [anchoredIndex_card]
  have hp : 0 < (d + C.order).choose d := Nat.choose_pos (by omega)
  omega

def paperDyadicTotalDegree {d : ℕ} (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  paperDyadicApproximationDegree C a offset H n j + anchoredDimension d C.order + 1

/-- Eventually the coordinate subtraction has no truncation: the actual total
lift degree is exactly the floor of the quadratic profile at every level. -/
theorem eventually_paper_total_degree_eq_floor {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℝ in atTop, ∀ j : ℕ,
      paperDyadicTotalDegree C a offset H n j =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset H n j)) := by
  have hβ : 0 < paperDegreeSlope C := div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)
  filter_upwards [eventually_width_degree_threshold ha hβ offset (paperPolynomialDimension C),
    (allocationWidth_tendsto_atTop ha offset).eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn hS
  intro j
  have hq : paperPolynomialDimension C ≤ Nat.floor
      (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset H n j)) :=
    profile_coordinate_order_admissible _ hβ.le hS (by linarith)
  unfold paperDyadicTotalDegree paperDyadicApproximationDegree actualApproximationDegree allocatedApproximationDegree
  rw [Nat.add_assoc, ← paperPolynomialDimension_eq_anchoredDimension_add_one C]
  exact Nat.sub_add_cancel hq

/-- The exact lift degrees have the paper's uniform logarithmic growth. -/
theorem eventually_paper_total_degree_log_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∀ᶠ n : ℝ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      (paperDyadicTotalDegree C a offset H n j : ℝ) ≤
        allocationDegreeCoefficient a (paperDegreeSlope C) * (Real.log n) ^ (3 / 2 : ℝ) := by
  have hβ : 0 ≤ paperDegreeSlope C := (div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)).le
  have hγ : 0 ≤ paperDegreeReserve C := by
    unfold paperDegreeReserve
    exact div_nonneg (by positivity) (paperSpatialExponent_pos C hs).le
  have hb := eventually_allocation_degree_bound ha hβ offset
    (fun n => Finset.range (terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n + 1))
    (allocationLevelPosition (paperDyadicStep C) a offset H)
    (eventually_actual_allocation_level_range (paperDyadicStep_pos C) ha hH hγ offset)
  filter_upwards [eventually_paper_total_degree_eq_floor C hs a offset H ha, hb] with n he hn
  intro j hj
  rw [he]
  exact hn j (Finset.mem_range.mpr (by change j < paperDyadicTerminalLevel C a offset H n + 1; omega))

/-- Every fixed positive sample fraction dominates all actual lift degrees. -/
theorem eventually_paper_total_degree_lt_fraction {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℝ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      (paperDyadicTotalDegree C a offset H n j : ℝ) < ε * n := by
  filter_upwards [eventually_paper_total_degree_log_bound C hs a offset H ha hH,
    eventually_log_power_lt_sample (3 / 2) (allocationDegreeCoefficient a (paperDegreeSlope C)) hε]
    with n hn he
  intro j hj
  exact (hn j hj).trans_lt he

/-- The actual two-pilot split permits the exact factorial lifts and the
variance denominator Λ=N/2, uniformly over every allocated level. -/
theorem eventually_paper_degree_three_block_guards {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      paperDyadicTotalDegree C a offset H n j ≤ threeBlockSize n ∧
      0 < (threeBlockSize n : ℝ) / 2 ∧
      (threeBlockSize n : ℝ) / 2 ≤
        (threeBlockSize n : ℝ) - (paperDyadicTotalDegree C a offset H n j : ℝ) + 1 := by
  have hb : ∀ᶠ n : ℕ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      (paperDyadicTotalDegree C a offset H n j : ℝ) < (1 / 8 : ℝ) * n :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_paper_total_degree_lt_fraction C hs a offset H ha hH (by norm_num))
  filter_upwards [hb, eventually_ge_atTop (6 : ℕ)] with n hn h6
  intro j hj
  have hm := threeBlockSize_fraction h6
  have hd := hn j hj
  have hhalf : (paperDyadicTotalDegree C a offset H n j : ℝ) ≤ (threeBlockSize n : ℝ) / 2 := by
    linarith
  have hmpos : 0 < (threeBlockSize n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (2 : ℕ)) (threeBlockSize_two_le h6))
  refine ⟨?_, by positivity, by linarith⟩
  exact_mod_cast (hhalf.trans (by linarith : (threeBlockSize n : ℝ) / 2 ≤ threeBlockSize n))

/-- Thus the genuine original-sample lifts at the paper's actual allocated
degrees are square-integrable and unbiased on each independent pilot block. -/
theorem eventually_paper_allocated_pilot_moment_facts {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness)
    (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∀ᶠ n : ℕ in atTop, ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j ≤ paperDyadicTerminalLevel C a offset H n, ∀ x ∈ unitCube d, ∀ y : ℝ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
      MemLp (dyadicPolynomialPilot C (threeBlockSize n) j x y
        (paperDyadicApproximationDegree C a offset H n j) row) 2 (sampleLaw θ (threeBlockSize n)) ∧
      (∫ z, dyadicPolynomialPilot C (threeBlockSize n) j x y
        (paperDyadicApproximationDegree C a offset H n j) row z ∂sampleLaw θ (threeBlockSize n)) =
      incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y (paperDyadicApproximationDegree C a offset H n j) row
        (dyadicIncrementRawMean θ j x) := by
  letI : Nonempty (AnchoredIndex d C.order) := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  filter_upwards [eventually_paper_degree_three_block_guards C hs a offset H ha hH] with n hn
  intro θ hθ j hj x hx y row
  exact dyadicPolynomialPilot_moment_facts C θ hθ (threeBlockSize n) j x hx y _ row (hn j hj).1

end NearlyMinimax
