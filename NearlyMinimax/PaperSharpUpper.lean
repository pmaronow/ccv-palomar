module

public import NearlyMinimax.AllocatedPilotAssumptions
public import NearlyMinimax.DyadicRawCoefficients
public import NearlyMinimax.CoefficientPairEstimator
public import NearlyMinimax.UpperMasterRate


@[expose] public section

/-! The exact original sharp minimax upper bound. All constants and the
sample cutoff precede the extension-domain quantifier. The estimator consists
only of observable factorial lifts and the stabilized pair statistic. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem paper_upper_sharp_estimator {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n → ∃ T : Estimator d n,
        ∀ θ, Admissible (C.withDomain U) θ →
          meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (K * paperUpperScale C n) := by
  obtain ⟨A, Cp, hA, hCp, hp⟩ := uniform_domain_eventually_allocated_pair_pilot_assumptions C hreg
  let C₀ := max 1 (12 * paperPilotMomentFactor (pilotModelConstants C) A)
  let C_D := max 1 (4 * paperDegreeSlope C)
  have hC : 1 ≤ C₀ := le_max_left _ _
  have hD : 1 ≤ C_D := le_max_left _ _
  have hCpos : 0 < C₀ := zero_lt_one.trans_le hC
  have hDpos : 0 < C_D := zero_lt_one.trans_le hD
  have hDβ : 4 * paperDegreeSlope (pilotModelConstants C) ≤ C_D := le_max_right _ _
  have hcoef : 12 * paperPilotMomentFactor (pilotModelConstants C) A ≤ C₀ := le_max_right _ _
  let H := C₀ * C_D
  have hH : 0 < H := mul_pos hCpos hDpos
  obtain ⟨_, B, _, hB, hpop⟩ := uniform_domain_allocated_population_pair_witnesses C hreg hH
  obtain ⟨S, hS, hscale⟩ := paper_allocated_risk_scale_upper C hreg hH
  let K := Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
    paperAllocatedMasterConstant C B * S
  have hK : 0 < K := mul_pos (mul_pos
    (Real.sqrt_pos.mpr (pairRateSquaredConstant_pos C hCp.le (by norm_num) (by norm_num)))
    (paperAllocatedMasterConstant_pos C B)) hS
  have hW := eventually_paperAllocatedPilotBudget_le_one (pilotModelConstants C)
    hreg A C₀ C_D hC hD hDβ hcoef
  have hall : ∀ᶠ n : ℕ in atTop, ∀ U : ExtensionDomain d,
      ∃ T : Estimator d n, ∀ θ, Admissible (C.withDomain U) θ →
        meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (K * paperUpperScale C n) := by
    filter_upwards [hp C₀ C_D hCpos hDpos, hpop, hscale, hW,
      eventually_paper_allocated_master_rate C hreg hH B,
      eventually_ge_atTop (6 : ℕ)] with n hpn hpopn hscalen hWn hmastern hn6
    intro U
    let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n
    let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) H n
    let L := paperAllocatedFinestLevel C H n
    let k := (2 : ℕ) ^ L
    let W := paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n
    let c := dyadicRawCoefficients C (threeBlockSize n) J m
    have hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
        (Covariate d × Covariate d) => c z.1 z.2) :=
      dyadicRawCoefficients_joint_measurable C _ J m
    let T := coefficientPairEstimator (C.withDomain U) k (by dsimp only [k]; positivity) c hmc
    refine ⟨T, ?_⟩
    intro θ hθ
    let bar := dyadicPopulationCoefficients C θ J m
    let η := dyadicNoiseCoefficients C θ (threeBlockSize n) J m
    have heq : c = pairPilotCoefficient bar η := by
      funext z w
      exact dyadicRawCoefficients_eq_population_add_noise C θ _ J m z w
    have hpr : PairPilotAssumptions θ k (by dsimp only [k]; positivity)
        (sampleLaw θ (threeBlockSize n)) bar η Cp W (Cp ^ 2 * W / (n : ℝ)) := hpn U θ hθ
    have hpopulation := hpopn U θ hθ
    have hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k (by dsimp only [k]; positivity), bar w 0 = 1 :=
      Filter.Eventually.of_forall hpopulation.2.1
    let b := B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n *
      (dyadicPilotScale d J) ^ (-paperSpatialExponent C)
    have hr := coefficientPairEstimator_rms_bound (C.withDomain U) θ hθ hn6 k
      (by dsimp only [k]; positivity) c hmc bar η Cp W b heq hpr hfirst hpopulation.2.2.2
    apply hr.trans
    apply ENNReal.ofReal_mono
    have hw0 : 0 ≤ W := paperAllocatedPilotBudget_nonneg (pilotModelConstants C) A C₀ C_D n
    have hm := hmastern W hw0 hWn
    have hPC : 0 ≤ Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) := Real.sqrt_nonneg _
    have hMC : 0 ≤ paperAllocatedMasterConstant C B := (paperAllocatedMasterConstant_pos C B).le
    have h1 := mul_le_mul_of_nonneg_left hm hPC
    have h2 := mul_le_mul_of_nonneg_left hscalen (mul_nonneg hPC hMC)
    calc
      _ ≤ Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
          (paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n) := h1
      _ = (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
          paperAllocatedMasterConstant C B) * paperAllocatedRiskScale C H n := by ring
      _ ≤ (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
          paperAllocatedMasterConstant C B) * (S * paperUpperScale C n) := h2
      _ = K * paperUpperScale C n := by dsimp only [K]; ring
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
  refine ⟨K, hK, max 2 n₀, le_max_left _ _, ?_⟩
  intro U n hn
  exact hn₀ n ((le_max_right _ _).trans hn) U

theorem paper_upper_sharp {d : ℕ} (C : ModelConstants d) : UpperSharpClaim C := by
  intro hreg
  obtain ⟨K, hK, n₀, hn₀, hT⟩ := paper_upper_sharp_estimator C hreg
  refine ⟨K, hK, n₀, hn₀, ?_⟩
  intro U n hn
  obtain ⟨T, hr⟩ := hT U n hn
  exact minimaxRMS_le_of_estimator_rms (C.withDomain U) T hr

end NearlyMinimax
