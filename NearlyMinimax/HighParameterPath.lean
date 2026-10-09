module

public import NearlyMinimax.HighObservationReal


@[expose] public section

/-! An actual original-model parameter path for every raw source state.
A fixed valid endpoint defines the path outside the time interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def highNormalizedParameterPath (T : ℝ) (hT : 0 ≤ T) (a v η : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y)
    (t : ℝ) (ω : Ω) : RegressionParameter d :=
  if ht : t ∈ Icc 0 T then
    normalizedDensityTernaryParameter (p ω) (F ω) a (v-η^2*t) hF.of_uncurry_left ha (hq t ht ω)
  else
    normalizedDensityTernaryParameter (p ω) (F ω) a v hF.of_uncurry_left ha
      (fun x y => by simpa using hq 0 ⟨le_rfl,hT⟩ ω x y)

theorem highNormalizedParameterPath_apply (T : ℝ) (hT : 0 ≤ T) (a v η : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y)
    (t : ℝ) (ht : t ∈ Icc 0 T) (ω : Ω) :
    highNormalizedParameterPath T hT a v η ha p F hF hq t ω =
      normalizedDensityTernaryParameter (p ω) (F ω) a (v-η^2*t) hF.of_uncurry_left ha (hq t ht ω) := by
  unfold highNormalizedParameterPath
  rw [dif_pos ht]

theorem highNormalizedParameterPath_variance (T : ℝ) (hT : 0 ≤ T) (a v η : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y)
    (t : ℝ) (ht : t ∈ Icc 0 T) (ω : Ω) :
    (highNormalizedParameterPath T hT a v η ha p F hF hq t ω).variance = v-η^2*t := by
  rw [highNormalizedParameterPath_apply T hT a v η ha p F hF hq t ht ω]
  rfl

theorem highNormalizedParameterPath_sampleLaw (T : ℝ) (hT : 0 ≤ T) (a v η : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y)
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (ω : Ω) :
    highRealSampleKernel n a (v-η^2*t) p F hp hF ω =
      sampleLaw (highNormalizedParameterPath T hT a v η ha p F hF hq t ω) n := by
  rw [highNormalizedParameterPath_apply T hT a v η ha p F hF hq t ht ω]
  exact highRealSampleKernel_eq_sampleLaw n a (v-η^2*t) p F hp hF aRaw bRaw haRaw hraw ha (hq t ht) ω

end NearlyMinimax
