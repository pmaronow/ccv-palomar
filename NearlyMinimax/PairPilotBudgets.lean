module

public import NearlyMinimax.CommonPairRisk


@[expose] public section

/-! The paper's pointwise pilot budget supplies the actual spatial energy. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
include hθ hp

theorem pairPilotVarianceBase_le :
    pairPilotVarianceBase θ k hk μ bar η ≤ C.densityUpper * (2 * Cp ^ 2 + Cp * W) := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hb := regularPairDesignMeasure_ae_of_supported θ k hk hp.barBound
  have hs := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseSection
  have he := regularPairDesignMeasure_ae_of_supported θ k hk hp.noiseEnergy
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable Cp hb
  have hbarE : (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) ≤
      Cp ^ 2 * (regularPairDesignMeasure θ k hk).real univ := by
    have h := integral_mono_ae hbar.norm.integrable_sq (integrable_const (Cp ^ 2))
      (hb.mono (fun w hw => pow_le_pow_left₀ (norm_nonneg _) hw 2))
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  have hnoiseE := PilotFields.joint_energy_le_of_uniform_sections hp.noiseMeasurable hs
    (mul_nonneg hp.constantNonnegative hp.budgetNonnegative) he
  have hmass := (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2
  have hbarU := mul_le_mul_of_nonneg_left hmass (sq_nonneg Cp)
  have hnoiseU := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hp.constantNonnegative hp.budgetNonnegative)
  unfold pairPilotVarianceBase
  nlinarith

end NearlyMinimax
