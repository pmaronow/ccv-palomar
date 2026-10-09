module

public import NearlyMinimax.Model
public import RoughRegime.Applications


@[expose] public section

/-! Extended-valued RMS risk agrees with the infimum of supremum L2 errors.
These identities do not assume second-moment finiteness of the estimator.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

theorem meanSquaredRisk_rpow_eq_eLpNorm {d n : ℕ} (T : Estimator d n)
    (θ : RegressionParameter d) :
    meanSquaredRisk T θ ^ (1 / 2 : ℝ) =
      eLpNorm (fun z => T.val z - θ.variance) 2 (sampleLaw θ n) := by
  symm
  exact RoughRegime.Applications.eLpNorm_two_eq_squaredIntegral (sampleLaw θ n)
    (fun z => T.val z - θ.variance) (T.property.sub measurable_const)

theorem minimaxRMS_eq_inf_sup_rms {d : ℕ} (C : ModelConstants d) (n : ℕ) :
    minimaxRMS C n = ⨅ T : Estimator d n,
      ⨆ θ : {θ : RegressionParameter d // Admissible C θ},
        meanSquaredRisk T θ.val ^ (1 / 2 : ℝ) := by
  let φ := ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)
  change φ (⨅ T : Estimator d n, ⨆ θ : {θ // Admissible C θ}, meanSquaredRisk T θ.val) = _
  rw [φ.map_iInf]
  simp_rw [φ.map_iSup]
  rfl

theorem minimaxRMS_eq_inf_sup_eLpNorm {d : ℕ} (C : ModelConstants d) (n : ℕ) :
    minimaxRMS C n = ⨅ T : Estimator d n,
      ⨆ θ : {θ : RegressionParameter d // Admissible C θ},
        eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n) := by
  rw [minimaxRMS_eq_inf_sup_rms]
  simp_rw [meanSquaredRisk_rpow_eq_eLpNorm]

end NearlyMinimax
