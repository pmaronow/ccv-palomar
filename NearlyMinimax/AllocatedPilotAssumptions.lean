module

public import NearlyMinimax.UniformPilotStatistics
public import NearlyMinimax.UniformPopulationPairBounds
public import NearlyMinimax.PairPilotFromScalars
public import NearlyMinimax.PaperVarianceReserve


@[expose] public section

/-! Primitive pair-pilot assumptions derived from actual original-model
factorial lifts. All constants precede the extension domain; the paper's
allocated profile discharges every sample-degree guard. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem uniform_domain_dyadic_pair_pilot_assumptions {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ A Cp : ℝ, 0 < A ∧ 0 < Cp ∧
      ∀ U : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain U) θ →
      ∀ (n : ℝ), 0 < n → ∀ N J L : ℕ, J ≤ L → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ N) →
      ∀ Λ : ℝ, 0 < Λ → n / 12 ≤ Λ →
      (∀ j : Fin (J + 1), Λ ≤ (N : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      PairPilotAssumptions θ ((2 : ℕ) ^ L) (by positivity) (sampleLaw θ N)
        (dyadicPopulationCoefficients C θ J m)
        (fun z w => twoScalarPilotVector (dyadicMultilevelErrorField C θ N J 0 m z w)
          (dyadicMultilevelErrorField C θ N J 1 m z w))
        Cp (dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L)
        (Cp ^ 2 * dyadicMultilevelBudget
          (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L / n) := by
  letI : Nonempty (AnchoredIndex d C.order) := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨D, A, hD, hA, hb⟩ := uniform_domain_common_dyadicMultilevel_bounds C
  obtain ⟨Cp₀, hCp₀, hbar⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound C hs
  let point : ℝ := 4 * ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ)
  let test : ℝ := 4 * C.densityUpper ^ 2 * (2 : ℝ) ^ d *
    ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ)
  let Cp : ℝ := max Cp₀ (max 1 (5 * point + 72 * test + 1))
  have hp0 : 0 ≤ point := by dsimp [point]; positivity
  have ht0 : 0 ≤ test := by dsimp [test]; positivity
  have hCp₀le : Cp₀ ≤ Cp := le_max_left _ _
  have hC1 : 1 ≤ Cp := (le_max_left _ _).trans (le_max_right _ _)
  have hCall : 5 * point + 72 * test + 1 ≤ Cp := (le_max_right _ _).trans (le_max_right _ _)
  have hCp : 0 < Cp := zero_lt_one.trans_le hC1
  have hpoint : 5 * point ≤ Cp := by linarith only [hCall, ht0]
  have htest : 72 * test ≤ Cp ^ 2 := by
    have hc : 72 * test ≤ Cp := by linarith only [hCall, hp0]
    have hsq : Cp ≤ Cp ^ 2 := by nlinarith only [hC1]
    exact hc.trans hsq
  refine ⟨A, Cp, hA, hCp, ?_⟩
  intro U θ hθ n hn N J L hJL m hdegree Λ hΛ hΛn hΛdegree
  let CU := C.withDomain U
  letI : Nonempty (AnchoredIndex d CU.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  let := sampleLaw_isProbability CU θ hθ N
  let := designLaw_isProbability CU θ hθ
  let W := dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (dyadicSeriesEnvelope_nonneg _ _ _ hΛ.le _ _)
  have hy0 : |(0 : ℝ)| ≤ max C.holderBound 1 := by
    simpa only [abs_zero] using (zero_le_one.trans (le_max_right C.holderBound 1))
  have hy1 : |(1 : ℝ)| ≤ max C.holderBound 1 := by simpa only [abs_one] using le_max_right C.holderBound 1
  have hbounds (y : ℝ) (hy : |y| ≤ max C.holderBound 1) :=
    hb U θ hθ N J L hJL y hy m hdegree Λ hΛ hΛdegree
  have hcubes : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ), w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ), (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ)] with w hx hz
    exact ⟨hx, hz⟩
  have hf (y : ℝ) (w : Covariate d × Covariate d) (hx : w.1 ∈ unitCube d) :=
    dyadicMultilevelErrorField_point_moment_facts CU θ hθ N J w.1 hx w.2 y m hdegree
  have hsections : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell ((2 : ℕ) ^ L) (by positivity)) w ≠ 0 →
        MemLp (fun z => dyadicMultilevelErrorField C θ N J 0 m z w) 2 (sampleLaw θ N) ∧
        MemLp (fun z => dyadicMultilevelErrorField C θ N J 1 m z w) 2 (sampleLaw θ N) := by
    filter_upwards [hcubes] with w hw _
    exact ⟨(hf 0 w hw.1).1, (hf 1 w hw.1).1⟩
  have henergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell ((2 : ℕ) ^ L) (by positivity)) w ≠ 0 →
        (∫ z, dyadicMultilevelErrorField C θ N J 0 m z w ^ 2 ∂sampleLaw θ N) ≤ point * W ∧
        (∫ z, dyadicMultilevelErrorField C θ N J 1 m z w ^ 2 ∂sampleLaw θ N) ≤ point * W := by
    filter_upwards [hcubes] with w hw hs
    have hc : regularGridCell ((2 : ℕ) ^ L) (by positivity) w.1 =
        regularGridCell ((2 : ℕ) ^ L) (by positivity) w.2 := by
      by_contra h
      apply hs
      simp [sameLabelKernel, h]
    exact ⟨(hbounds 0 hy0).1 w.1 hw.1 w.2 hw.2 hc,
      (hbounds 1 hy1).1 w.1 hw.1 w.2 hw.2 hc⟩
  have hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity),
      (∫ z, dyadicMultilevelErrorField C θ N J 0 m z w ∂sampleLaw θ N) = 0 ∧
      (∫ z, dyadicMultilevelErrorField C θ N J 1 m z w ∂sampleLaw θ N) = 0 := by
    filter_upwards [regularPairDesignMeasure_cube_ae CU θ hθ ((2 : ℕ) ^ L) (by positivity)] with w hw
    exact ⟨(hf 0 w hw.1).2, (hf 1 w hw.1).2⟩
  have hp := pairPilotAssumptions_of_two_scalars (sampleLaw θ N) θ ((2 : ℕ) ^ L) (by positivity)
    (dyadicPopulationCoefficients C θ J m)
    (dyadicMultilevelErrorField C θ N J 0 m) (dyadicMultilevelErrorField C θ N J 1 m)
    hCp.le hW ht0 hΛ hpoint
    (dyadicPopulationCoefficients_measurable CU θ hθ J m)
    (dyadicMultilevelErrorField_joint_measurable CU θ hθ N J 0 m hdegree)
    (dyadicMultilevelErrorField_joint_measurable CU θ hθ N J 1 m hdegree)
    ((hbar U θ hθ J L hJL m).mono (fun _ hw hs => (hw hs).trans hCp₀le))
    hsections henergy hcenter
    (dyadicMultilevelErrorField_envelope_weighted_integrable CU θ hθ N J L hJL 0 hy0 m hdegree)
    (dyadicMultilevelErrorField_envelope_weighted_integrable CU θ hθ N J L hJL 1 hy1 m hdegree)
    (fun v hv => (dyadicMultilevelErrorField_envelope_test_moment_facts CU θ hθ N J L hJL 0 hy0 m hdegree v hv).1)
    (fun v hv => (dyadicMultilevelErrorField_envelope_test_moment_facts CU θ hθ N J L hJL 1 hy1 m hdegree v hv).1)
    (hbounds 0 hy0).2 (hbounds 1 hy1).2
  exact hp.mono_lam (scalarPilot_covariance_sample_budget hn hW ht0 hΛn htest)

/-- The actual paper profile produces the primitive pair assumptions under
original sample laws, uniformly over every extension domain. No degree,
covariance, or pilot-budget inequality is an input to this endpoint. -/
theorem uniform_domain_eventually_allocated_pair_pilot_assumptions {d : ℕ}
    (C : ModelConstants d) (hreg : highSmoothnessRegime C) :
    ∃ A Cp : ℝ, 0 < A ∧ 0 < Cp ∧ ∀ C₀ C_D : ℝ, 0 < C₀ → 0 < C_D →
      ∀ᶠ n : ℕ in atTop, ∀ U : ExtensionDomain d, ∀ θ : RegressionParameter d,
      Admissible (C.withDomain U) θ →
      PairPilotAssumptions θ ((2 : ℕ) ^ paperAllocatedFinestLevel C (C₀ * C_D) n)
        (by positivity) (sampleLaw θ (threeBlockSize n))
        (dyadicPopulationCoefficients C θ
          (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
          (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n))
        (fun z w => twoScalarPilotVector
          (dyadicMultilevelErrorField C θ (threeBlockSize n)
            (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
            0 (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n) z w)
          (dyadicMultilevelErrorField C θ (threeBlockSize n)
            (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
            1 (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n) z w))
        Cp (paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n)
        (Cp ^ 2 * paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n / (n : ℝ)) := by
  obtain ⟨A, Cp, hA, hCp, hp⟩ := uniform_domain_dyadic_pair_pilot_assumptions C hreg.1
  refine ⟨A, Cp, hA, hCp, ?_⟩
  intro C₀ C_D hC hD
  have hH : 0 < C₀ * C_D := mul_pos hC hD
  have hg : ∀ᶠ n : ℕ in atTop,
      paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n ≤
        paperAllocatedFinestLevel C (C₀ * C_D) n :=
    tendsto_natCast_atTop_atTop.eventually
      ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.2)
  filter_upwards [hg, eventually_paper_degree_three_block_guards C hreg.1
    (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) (paperUpperSaddle_pos C hreg) hH,
    eventually_ge_atTop (6 : ℕ)] with n hg hdeg h6
  intro U θ hθ
  let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n
  let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hΛ : 0 < (threeBlockSize n : ℝ) / 2 := (hdeg 0 (Nat.zero_le _)).2.1
  have hΛn : (n : ℝ) / 12 ≤ (threeBlockSize n : ℝ) / 2 := by
    have hf := threeBlockSize_fraction h6
    linarith only [hf, hn]
  have hd (j : Fin (J + 1)) : m j.val + anchoredDimension d C.order + 1 ≤ threeBlockSize n :=
    (hdeg j.val (Nat.le_of_lt_succ j.isLt)).1
  have hΛd (j : Fin (J + 1)) : (threeBlockSize n : ℝ) / 2 ≤ (threeBlockSize n : ℝ) -
      (m j.val + anchoredDimension d C.order + 1) + 1 := by
    simpa only [paperDyadicTotalDegree, Nat.cast_add, Nat.cast_one, m] using
      (hdeg j.val (Nat.le_of_lt_succ j.isLt)).2.2
  exact hp U θ hθ n hn (threeBlockSize n) J
    (paperAllocatedFinestLevel C (C₀ * C_D) n) hg m hd
    ((threeBlockSize n : ℝ) / 2) hΛ hΛn hΛd

end NearlyMinimax
