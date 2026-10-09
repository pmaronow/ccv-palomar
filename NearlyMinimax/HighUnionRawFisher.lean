module

public import NearlyMinimax.HighUnionFisher
public import NearlyMinimax.HighRawScoreEnergy


@[expose] public section

/-! The genuine spatial factorial budget yields joint raw Fisher
integrability and the mass-normalized energy for the actual source prior. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedAppend highRawSampleLikelihood massPowerNormalizer

/-- Exact spatial factorial series in the original normalized experiment. -/
def highSourceSpatialSeries (d k n : ℕ) [NeZero k] (pMinus cMass : ℝ)
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ) : ℝ :=
  (3^d : ℕ)*∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n+1),
    ((n : ℝ)*highFixedScoreDenominator pMinus cMass*(2/(k : ℝ))^d)^r /
      (r.factorial : ℝ)*∫ u, H j r u
        ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)

include G hpos in
 theorem highUnionSource_raw_fisher_bound
    (ν : Measure (HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)))
    [IsProbabilityMeasure ν] (n : ℕ) (hk : 4 ≤ k)
    (a V η cMass : ℝ) (ha : a ≠ 0) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (highUnionSourceRegression C R η h x) V y)
    (hDensity : ∀ j h (x : Fin n → Covariate d),
      (∫ e, highUnionActivation R (highCenterMix C) e *
        ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0)
    (H : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E) →
      HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ h j r, Integrable (H h j r)
      (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ h j r u, 0 ≤ H h j r u)
    (hdom : ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r a V η h j) x ≤
        H h j r (highPatchProductChart d k j x))
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ h, highSourceSpatialSeries d k n C.densityLower cMass (H h) ≤ B) :
    let D := highHistoryLikelihoodDerivative (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η)
    let L := fun h => highRawSampleLikelihood n a V
      (highUnionSourceDensity C R h) (highUnionSourceRegression C R η h)
    let m := fun h => highRawDensityMass (highUnionSourceDensity C R h)
    Integrable (fun z => D z.1 z.2 ^ 2 / L z.1 z.2) (ν.prod (highSampleReference d n)) ∧
    (massPowerNormalizer ν m n)⁻¹ *
      (∫ z, D z.1 z.2 ^ 2 / L z.1 z.2 ∂ν.prod (highSampleReference d n)) ≤ B := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R η
  have hp : Measurable (Function.uncurry p) := highUnionSourceDensity_joint_measurable C R G
  have hF : Measurable (Function.uncurry F) := highUnionSourceRegression_joint_measurable C R G η
  let D := highHistoryLikelihoodDerivative (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C)) n a V η p F
  have hDm : Measurable (Function.uncurry D) := highHistoryLikelihoodDerivative_measurable
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
    (highUnionActivation_measurable R G.activation_measurable _) n a V η p F hp hF
  have hs (h) := highUnionSource_sample_fisher_bound C R G hpos n hk a V η cMass ha hcMass
    hq hDensity h (H h) (hH h) (hH0 h) (hdom h)
  have hj := high_raw_joint_fisher_integrable_bound ν n a V p F hp hF
    C.densityLower C.densityUpper C.densityLower_pos
    (highUnionSourceDensity_coarse_interval C R G) (fun h x y => hcMass.trans_le (hq h x y))
    D hDm B hB
    (fun h => by simpa only [highHistoryLikelihoodScore] using (hs h).1)
    (fun h => by
      have hb0 := hbudget h
      unfold highSourceSpatialSeries at hb0
      have hb := (hs h).2.trans hb0
      simpa only [highHistoryLikelihoodScore] using hb)
  have hG : 0 < massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n :=
    massPowerNormalizer_pos ν _ (highRawDensityMass_joint_measurable p hp) n
      C.densityLower C.densityUpper C.densityLower_pos
      (fun h => highRawDensityMass_mem_Icc (p h) hp.of_uncurry_left
        C.densityLower C.densityUpper C.densityLower_pos
        (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h)))
  refine ⟨hj.1, ?_⟩
  calc
    _ ≤ (massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n)⁻¹ *
        (massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n * B) :=
      mul_le_mul_of_nonneg_left hj.2 (inv_nonneg.mpr hG.le)
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hG.ne', one_mul]

end NearlyMinimax
