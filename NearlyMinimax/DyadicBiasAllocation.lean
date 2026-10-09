module

public import NearlyMinimax.PopulationPilotCoefficients
public import NearlyMinimax.ActualBiasAllocation


@[expose] public section

/-! Actual dyadic population bias at the explicit allocation of the paper.
No per-level or total approximation-budget premise is assumed. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def paperDyadicStep {d : ℕ} (_C : ModelConstants d) : ℝ := (d : ℝ) * Real.log 2

def paperSpatialExponent {d : ℕ} (C : ModelConstants d) : ℝ := (C.smoothness - 1) / (d : ℝ)

def paperDegreeSlope {d : ℕ} (C : ModelConstants d) : ℝ := paperSpatialExponent C / paperTau C

def paperDegreeReserve {d : ℕ} (C : ModelConstants d) : ℝ :=
  ((anchoredDimension d C.order : ℝ) + 1 / 2) / paperSpatialExponent C

def paperDyadicTerminalLevel {d : ℕ} (C : ModelConstants d) (a offset H n : ℝ) : ℕ :=
  terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n

def paperDyadicApproximationDegree {d : ℕ} (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  actualApproximationDegree (paperDyadicStep C) a offset H (paperDegreeSlope C) n j (paperPolynomialDimension C)

theorem paperDyadicStep_pos {d : ℕ} (C : ModelConstants d) : 0 < paperDyadicStep C :=
  mul_pos (Nat.cast_pos.mpr C.dimension_pos) (Real.log_pos (by norm_num))

theorem paperSpatialExponent_pos {d : ℕ} (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperSpatialExponent C := div_pos (sub_pos.mpr hs) (Nat.cast_pos.mpr C.dimension_pos)

theorem dyadicPilotScale_eq_exp {d : ℕ} (C : ModelConstants d) (j : ℕ) :
    dyadicPilotScale d j = Real.exp (paperDyadicStep C * (j : ℝ)) := by
  have hl : Real.log (dyadicPilotScale d j) = paperDyadicStep C * (j : ℝ) := by
    unfold dyadicPilotScale paperDyadicStep
    rw [Real.log_pow, Real.log_pow]
    ring
  rw [← hl, Real.exp_log (dyadicPilotScale_pos d j)]

theorem dyadic_spatial_weight_eq {d : ℕ} (C : ModelConstants d) (j : ℕ) :
    (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) =
      (dyadicPilotScale d j) ^ (-paperSpatialExponent C) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (dyadicPilotScale_pos d j)]
  rw [Real.log_inv]
  unfold dyadicPilotScale paperSpatialExponent
  rw [Real.log_pow, Real.log_pow, Real.log_pow]
  congr 1
  have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  field_simp

theorem exp_negative_nat_eq_pow (τ : ℝ) (m : ℕ) :
    Real.exp (-(m : ℝ) * τ) = (Real.exp (-τ)) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The actual anchored bias budget is exactly the scalar cell-mass budget. -/
theorem dyadicPopulationBiasBudget_eq_scalar {d : ℕ} (C : ModelConstants d)
    (J : ℕ) (m : ℕ → ℕ) :
    dyadicPopulationBiasBudget C J m =
      (Real.exp (paperDyadicStep C * (J : ℝ))) ^ (-paperSpatialExponent C) +
      ∑ j ∈ Finset.range (J + 1), (Real.exp (paperDyadicStep C * (j : ℝ))) ^ (-paperSpatialExponent C) *
        ((m j : ℝ) + 1) ^ anchoredDimension d C.order * (Real.exp (-paperTau C)) ^ m j := by
  unfold dyadicPopulationBiasBudget
  simp_rw [dyadic_spatial_weight_eq C, dyadicPilotScale_eq_exp C, exp_negative_nat_eq_pow,
    Nat.cast_add, Nat.cast_one]

/-- U12 for the actual population-bias budget and its actual floored degree
profile, with all scalar identities supplied by the original model constants. -/
theorem eventually_paper_dyadic_bias_budget {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℝ in atTop,
      dyadicPopulationBiasBudget C (paperDyadicTerminalLevel C a offset H n)
        (paperDyadicApproximationDegree C a offset H n) ≤
      B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
  have hθ := paperSpatialExponent_pos C hs
  have hτ := paperTau_pos C
  have hβ : 0 < paperDegreeSlope C := div_pos hθ hτ
  have hτβ : paperTau C * paperDegreeSlope C = paperSpatialExponent C := by
    unfold paperDegreeSlope
    exact mul_div_cancel₀ _ hτ.ne'
  have hθγ : paperSpatialExponent C * paperDegreeReserve C =
      (anchoredDimension d C.order : ℝ) + 1 / 2 := by
    unfold paperDegreeReserve
    exact mul_div_cancel₀ _ hθ.ne'
  obtain ⟨B, hB, hb⟩ := eventually_actual_allocation_bias_sum
    (anchoredDimension d C.order) (paperPolynomialDimension C) (paperDyadicStep C) a offset H
    (paperDegreeReserve C) (paperDegreeSlope C) (paperSpatialExponent C) (paperTau C)
    (paperDyadicStep_pos C) ha hH hβ hθ hτ hτβ hθγ
  refine ⟨1 + B, by positivity, ?_⟩
  filter_upwards [hb] with n hn
  rw [dyadicPopulationBiasBudget_eq_scalar, dyadicPilotScale_eq_exp C]
  change (Real.exp (paperDyadicStep C * (paperDyadicTerminalLevel C a offset H n : ℝ))) ^ (-paperSpatialExponent C) +
      _ ≤ (1 + B) * (Real.exp (paperDyadicStep C * (paperDyadicTerminalLevel C a offset H n : ℝ))) ^ (-paperSpatialExponent C)
  exact (add_le_add le_rfl hn).trans_eq (by unfold paperDyadicTerminalLevel; ring)

/-- The actual mean coefficient field satisfies the allocated residual
bound uniformly over every original admissible regression model. -/
theorem eventually_allocated_population_residual {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℝ in atTop,
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell (paperDyadicTerminalLevel C a offset H n) x →
      |⟪dyadicPopulationCoefficients C θ (paperDyadicTerminalLevel C a offset H n)
          (paperDyadicApproximationDegree C a offset H n) (x, y),
        pairResponseVector (θ.regression x) (θ.regression y)⟫| ≤
        B * euclideanNorm (y - x) *
          (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
  obtain ⟨E, hE, he⟩ := admissible_dyadicPopulationResidual_bound C hs
  obtain ⟨B, hB, hb⟩ := eventually_paper_dyadic_bias_budget C hs a offset H ha hH
  refine ⟨E * B, mul_pos hE hB, ?_⟩
  filter_upwards [hb] with n hn
  intro θ hθ x hx y hy hc
  rw [dyadicPopulationCoefficients_residual]
  apply (he θ hθ _ _ x hx y hy hc).trans
  have hd : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
  apply (mul_le_mul_of_nonneg_left hn (mul_nonneg hE.le hd)).trans_eq
  ring

end NearlyMinimax
