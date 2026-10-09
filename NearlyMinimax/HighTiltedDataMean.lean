module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.MixtureRisk


@[expose] public section

/-! Actual tilted observable means are the means under the observed-data
mixture kernel, on the original real sample space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem highTiltedObservableMean_eq_dataMean {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V aRaw bRaw B : ℝ) (ha : a ≠ 0) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    highTiltedObservableMean ν n a V p F hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) := by
  have hm := highRawDensityMass_joint_measurable p hp
  have hb (ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν _ hm n aRaw bRaw haRaw hb
  let _ := highRealSampleKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  have hi : Integrable H ((highRealSampleKernel n a V p F hp hF) ∘ₘ
      (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) := by
    apply Integrable.of_bound hH.aestronglyMeasurable B
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hHb z
  exact (probability_kernel_integral _ _ H hi).symm

end NearlyMinimax
