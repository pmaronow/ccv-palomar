module

public import NearlyMinimax.UniformPopulationBounds
public import NearlyMinimax.UpperSpatialAllocation


@[expose] public section

/-! Uniform-domain population witnesses at the actual weighted pair design. -/
noncomputable section
open Filter MeasureTheory Set
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ J Jh : ℕ, J ≤ Jh → ∀ m : ℕ → ℕ,
      ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell ((2 : ℕ) ^ Jh) (by positivity)) w ≠ 0 →
          ‖dyadicPopulationCoefficients C θ J m w‖ ≤ Cp := by
  obtain ⟨Cp, hCp, hb⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound C hs
  refine ⟨Cp, hCp, ?_⟩
  intro Udom θ hθ J Jh hJJh m
  let := designLaw_isProbability (C.withDomain Udom) θ hθ
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
  exact hb Udom θ hθ J m w.1 hx w.2 hy (dyadicPilotCell_subset_coarser J Jh hJJh w.1 hc)


/-- A single bias constant works for every extension domain and original
admissible parameter, at the actual allocation and every dyadic refinement. -/
theorem uniform_domain_eventually_allocated_population_pair_residual {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ Jh : ℕ, paperDyadicTerminalLevel C a offset H n ≤ Jh →
      ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ Jh) (by positivity),
        |⟪dyadicPopulationCoefficients C θ (paperDyadicTerminalLevel C a offset H n)
            (paperDyadicApproximationDegree C a offset H n) w,
          pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤
          B * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ Jh)⁻¹ *
            (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
  obtain ⟨E, hE, he⟩ := uniform_domain_admissible_dyadicPopulationResidual_bound C hs
  obtain ⟨B, hB, hb⟩ := eventually_paper_dyadic_bias_budget C hs a offset H ha hH
  refine ⟨E * B, mul_pos hE hB, ?_⟩
  have hbNat := tendsto_natCast_atTop_atTop.eventually hb
  filter_upwards [hbNat] with n hn
  intro Udom θ hθ Jh hJJh
  filter_upwards [regularPairDesignMeasure_cube_ae (C.withDomain Udom) θ hθ ((2 : ℕ) ^ Jh) (by positivity),
    regularPairDesignMeasure_dyadic_cell_ae θ Jh] with w hw hc
  rw [dyadicPopulationCoefficients_residual]
  have hr : euclideanNorm (w.2 - w.1) ≤ Real.sqrt (d : ℝ) * ((2 : ℝ) ^ Jh)⁻¹ := by
    have hcoord := regular_grid_same_cell_radius ((2 : ℕ) ^ Jh) (by positivity) w.2 w.1 hw.2 hw.1 hc
    simpa [Nat.cast_pow, one_div] using euclideanNorm_le_coordinate_radius (w.2 - w.1)
      (1 / (((2 : ℕ) ^ Jh : ℕ) : ℝ)) (by positivity) hcoord
  apply (he Udom θ hθ _ _ w.1 hw.1 w.2 hw.2
    (dyadicPilotCell_subset_coarser _ Jh hJJh w.1 hc)).trans
  have hdist : 0 ≤ euclideanNorm (w.2 - w.1) := by unfold euclideanNorm; positivity
  calc
    E * euclideanNorm (w.2 - w.1) * dyadicPopulationBiasBudget C
        (paperDyadicTerminalLevel C a offset H n) (paperDyadicApproximationDegree C a offset H n) ≤
      E * euclideanNorm (w.2 - w.1) *
        (B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C)) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg hE.le hdist)
    _ ≤ E * (Real.sqrt (d : ℝ) * ((2 : ℝ) ^ Jh)⁻¹) *
        (B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hE.le)
        (mul_nonneg hB.le (Real.rpow_nonneg (dyadicPilotScale_pos _ _).le _))
    _ = _ := by ring

/-- The population witnesses consumed by the concrete sharp upper estimator,
with all constants and the eventual sample cutoff uniform over extension domains. -/
theorem uniform_domain_allocated_population_pair_witnesses {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∃ Cp B : ℝ, 0 < Cp ∧ 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n
      let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) H n
      let Jh := paperAllocatedFinestLevel C H n
      Measurable (dyadicPopulationCoefficients C θ J m) ∧
      (∀ w, dyadicPopulationCoefficients C θ J m w 0 = 1) ∧
      (∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell ((2 : ℕ) ^ Jh) (by positivity)) w ≠ 0 →
          ‖dyadicPopulationCoefficients C θ J m w‖ ≤ Cp) ∧
      (∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ Jh) (by positivity),
        |⟪dyadicPopulationCoefficients C θ J m w,
          pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤
          B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n *
            (dyadicPilotScale d J) ^ (-paperSpatialExponent C)) := by
  obtain ⟨Cp, hCp, hc⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound C hreg.1
  obtain ⟨B, hB, hb⟩ := uniform_domain_eventually_allocated_population_pair_residual C hreg.1
    (paperUpperSaddle C) (paperUpperShift C) H (paperUpperSaddle_pos C hreg) hH
  have hg : ∀ᶠ n : ℕ in atTop,
      paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n ≤ paperAllocatedFinestLevel C H n :=
    tendsto_natCast_atTop_atTop.eventually ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.2)
  refine ⟨Cp, B, hCp, hB, ?_⟩
  filter_upwards [hb, hg] with n hb hg
  intro Udom θ hθ
  dsimp only
  refine ⟨?_, dyadicPopulationCoefficients_first C θ _ _, hc Udom θ hθ _ _ hg _, ?_⟩
  · exact dyadicPopulationCoefficients_measurable (C.withDomain Udom) θ hθ _ _
  · simpa only [paperAllocatedSide, dyadicRoundedSide_eq_inv_pow, paperAllocatedFinestLevel] using
      hb Udom θ hθ (paperAllocatedFinestLevel C H n) hg

end NearlyMinimax
