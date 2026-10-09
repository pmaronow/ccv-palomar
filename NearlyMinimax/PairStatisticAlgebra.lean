module

public import NearlyMinimax.PairPilotAssumptions


@[expose] public section

/-! The actual numerator and the exact score identity for the paper's estimator. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

namespace PairUStatistic
variable {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω] [MeasurableSpace E]

theorem fieldPairAverage_add_smul (n : ℕ) (weight V : ℝ)
    (G H : P → E × E → ℝ) (X : Fin n → Ω → E) (z : P × Ω) :
    fieldPairAverage n weight (fun p w => G p w + V * H p w) X z =
      fieldPairAverage n weight G X z + V * fieldPairAverage n weight H X z := by
  unfold fieldPairAverage pairAverage weightedSymmetrization
  simp only [Prod.swap_prod_mk]
  have hpoint : ∀ i j : Fin n,
      weight / 4 * (G z.1 (X i z.2, X j z.2) + V * H z.1 (X i z.2, X j z.2) +
        (G z.1 (X j z.2, X i z.2) + V * H z.1 (X j z.2, X i z.2))) =
      weight / 4 * (G z.1 (X i z.2, X j z.2) + G z.1 (X j z.2, X i z.2)) +
      V * (weight / 4 * (H z.1 (X i z.2, X j z.2) + H z.1 (X j z.2, X i z.2))) := by
    intros; ring
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end PairUStatistic

def pairPilotNumeratorKernel {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (p : Ω × Ω)
    (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪pairPilotCoefficient bar η p.1 (pairCovariates z),
      InnerProductSpace.rankOne ℝ (pairResponseVector z.1.2 z.2.2)
        (pairResponseVector z.1.2 z.2.2)
          (pairPilotCoefficient bar η p.2 (pairCovariates z))⟫

theorem pairPilotNumeratorKernel_eq_score_add_noise {Ω : Type*} {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) :
    pairPilotNumeratorKernel k hk bar η =
      (fun p z => pairPilotScoreKernel θ k hk bar η p z +
        θ.variance * pairPilotNoiseKernel k hk bar η p z) := by
  funext p z
  have hq : sameLabelKernel (regularObservationLabel k hk) z =
      sameLabelKernel (regularGridCell k hk) (z.1.1, z.2.1) := rfl
  simp only [pairPilotNumeratorKernel, pairPilotScoreKernel, pairPilotNoiseKernel,
    pairScoreFieldKernel, pairNoiseFieldKernel, pairCovariates, regularObservationLabel,
    pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_right, inner_smul_right]
  rw [hq]
  ring

end NearlyMinimax
