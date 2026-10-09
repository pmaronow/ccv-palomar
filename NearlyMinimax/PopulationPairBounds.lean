module

public import NearlyMinimax.PaperSeriesAllocation
public import NearlyMinimax.PairPilotAssumptions


@[expose] public section

/-! Actual population coefficient bounds on the genuine weighted pair design.
The fine grid may be any dyadic refinement of the population terminal level. -/
noncomputable section
open Filter MeasureTheory Set
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem dyadicPopulationCoefficients_first {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (J : ℕ) (m : ℕ → ℕ) (w : Covariate d × Covariate d) :
    dyadicPopulationCoefficients C θ J m w 0 = 1 := by
  rfl

theorem regularPairDesignMeasure_dyadic_cell_ae {d : ℕ} (θ : RegressionParameter d) (J : ℕ) :
    ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity),
      w.2 ∈ dyadicPilotCell J w.1 := by
  apply regularPairDesignMeasure_ae_of_supported
  filter_upwards [] with w hw
  change regularGridCell ((2 : ℕ) ^ J) (by positivity) w.2 =
    regularGridCell ((2 : ℕ) ^ J) (by positivity) w.1
  by_contra h
  apply hw
  simp [sameLabelKernel, Ne.symm h]

/-- The genuine population coefficient field has a model-only cap on every
supported fine-grid pair, uniformly in all terminal levels and degrees. -/
theorem admissible_dyadicPopulationCoefficients_supported_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ J Jh : ℕ, J ≤ Jh → ∀ m : ℕ → ℕ,
      ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell ((2 : ℕ) ^ Jh) (by positivity)) w ≠ 0 →
          ‖dyadicPopulationCoefficients C θ J m w‖ ≤ Cp := by
  obtain ⟨Cp, hCp, hb⟩ := admissible_dyadicPopulationCoefficients_uniform_bound C hs
  refine ⟨Cp, hCp, ?_⟩
  intro θ hθ J Jh hJJh m
  let := designLaw_isProbability C θ hθ
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ),
    (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ)] with w hx hy hw
  have hc : w.2 ∈ dyadicPilotCell Jh w.1 := by
    change regularGridCell ((2 : ℕ) ^ Jh) (by positivity) w.2 =
      regularGridCell ((2 : ℕ) ^ Jh) (by positivity) w.1
    by_contra h
    apply hw
    simp [sameLabelKernel, Ne.symm h]
  exact hb θ hθ J m w.1 hx w.2 hy (dyadicPilotCell_subset_coarser J Jh hJJh w.1 hc)

/-- The actual pointwise population residual has the genuine fine-grid
bandwidth factor, with no radius bound taken as an assumption. -/
theorem admissible_dyadicPopulationResidual_fine_pair_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ J Jh : ℕ, J ≤ Jh → ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell Jh x →
      |⟪dyadicPopulationCoefficients C θ J m (x, y),
        pairResponseVector (θ.regression x) (θ.regression y)⟫| ≤
        E * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ Jh)⁻¹ * dyadicPopulationBiasBudget C J m := by
  obtain ⟨E, hE, he⟩ := admissible_dyadicPopulationResidual_bound C hs
  refine ⟨E, hE, ?_⟩
  intro θ hθ J Jh hJJh m x hx y hy hc
  rw [dyadicPopulationCoefficients_residual]
  have hr : euclideanNorm (y - x) ≤ Real.sqrt (d : ℝ) * ((2 : ℝ) ^ Jh)⁻¹ := by
    have hcoord := regular_grid_same_cell_radius ((2 : ℕ) ^ Jh) (by positivity) y x hy hx hc
    simpa [Nat.cast_pow, one_div] using euclideanNorm_le_coordinate_radius (y - x)
      (1 / (((2 : ℕ) ^ Jh : ℕ) : ℝ)) (by positivity) hcoord
  have hb : 0 ≤ dyadicPopulationBiasBudget C J m := by
    unfold dyadicPopulationBiasBudget
    positivity
  apply (he θ hθ J m x hx y hy (dyadicPilotCell_subset_coarser J Jh hJJh x hc)).trans
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hE.le) hb).trans_eq (by ring)

/-- Original U8 after the actual allocation, as the exact almost-everywhere
residual premise consumed by the original common-pair risk theorem. -/
theorem eventually_allocated_population_pair_residual {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ Jh : ℕ,
      paperDyadicTerminalLevel C a offset H n ≤ Jh →
      ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ Jh) (by positivity),
        |⟪dyadicPopulationCoefficients C θ (paperDyadicTerminalLevel C a offset H n)
            (paperDyadicApproximationDegree C a offset H n) w,
          pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤
          B * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ Jh)⁻¹ *
            (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
  obtain ⟨B, hB, hb⟩ := eventually_allocated_population_residual C hs a offset H ha hH
  refine ⟨B, hB, ?_⟩
  have hbNat := tendsto_natCast_atTop_atTop.eventually hb
  filter_upwards [hbNat] with n hn
  intro θ hθ Jh hJJh
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ Jh) (by positivity),
    regularPairDesignMeasure_dyadic_cell_ae θ Jh] with w hw hc
  have hr : euclideanNorm (w.2 - w.1) ≤ Real.sqrt (d : ℝ) * ((2 : ℝ) ^ Jh)⁻¹ := by
    have hcoord := regular_grid_same_cell_radius ((2 : ℕ) ^ Jh) (by positivity) w.2 w.1 hw.2 hw.1 hc
    simpa [Nat.cast_pow, one_div] using euclideanNorm_le_coordinate_radius (w.2 - w.1)
      (1 / (((2 : ℕ) ^ Jh : ℕ) : ℝ)) (by positivity) hcoord
  apply (hn θ hθ w.1 hw.1 w.2 hw.2
    (dyadicPilotCell_subset_coarser _ Jh hJJh w.1 hc)).trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hB.le)
    (Real.rpow_nonneg (dyadicPilotScale_pos _ _).le _)).trans_eq
  ring

end NearlyMinimax
