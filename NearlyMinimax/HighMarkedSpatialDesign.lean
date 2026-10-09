module

public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.HighSpatialScoreTransfer


@[expose] public section

/-! Genuine original normalized-design factorial transfer for the complete
source generator. All probability, Borel, and integrability conclusions
are derived from primitive raw-state guards and Q^r spatial envelopes. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem high_marked_original_design_spatial_series {ι E : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (n : ℕ)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (hAct : Measurable activation)
    (a V η : ℝ) (ha : a ≠ 0) (pMinus pPlus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (p : Covariate d → ℝ) (hpMeas : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    (pReset : E → Covariate d → ℝ) (hpReset : Measurable (Function.uncurry pReset))
    (cReset : E → ι → ℝ) (hcReset : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Covariate d → ℝ) (hg : Measurable g) (hw : Measurable w)
    (φ : Covariate d → ι → ℝ) (hφ : ∀ γ, Measurable (fun x => φ x γ)) (c : ι → ℝ)
    (hq : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hwo : ∀ x, x ∉ highTorusPatch d k j → w x = 0)
    (hro : ∀ e x, x ∉ highTorusPatch d k j → pReset e x = p x)
    (H : (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ r, Integrable (H r) (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ r u, 0 ≤ H r u)
    (hdom : ∀ r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x ≤
        H r (highPatchProductChart d k j x)) :
    Integrable (highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c)
      (Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)) ∧
    (∫ x, highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x
      ∂Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)) ≤
      ∑ r ∈ Finset.range (n + 1),
        ((n : ℝ) * highFixedScoreDenominator pMinus cMass * (2 / (k : ℝ)) ^ d) ^ r /
          (r.factorial : ℝ) * ∫ u, H r u
            ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) := by
  let _ := cubeVolume_isProbability d
  have hprob := high_normalized_design_probability p hpMeas pMinus pPlus hpMinus
    (Filter.Eventually.of_forall hraw)
  have hm : pMinus ≤ highRawDensityMass p :=
    (highRawDensityMass_mem_Icc p hpMeas pMinus pPlus hpMinus (Filter.Eventually.of_forall hraw)).1
  have hR (r : ℕ) (y : Fin r → Fin 3) : Measurable (fun x =>
      highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y) :=
    highMarkedSampleNumerator_measurable r π activation hAct a V η p hpMeas pReset hpReset
      cReset hcReset g w hg hw φ hφ c y
  have hRaw (r : ℕ) := high_raw_square_patch_integrable_bound hk j
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c)
    (hR r) (H r) (hH r) (hH0 r) (hdom r)
  have hs := high_marked_design_raw_factorial_series (cubeVolume d) n
    (highTorusPatch d k j) (highTorusPatch_measurableSet d k j)
    (highRawDensityMass p) pMinus cMass hpMinus hcMass hm π activation a V η ha p hpMeas
    pReset cReset g w φ c
    (highMarkedResponseMass_measurable a V η g w hg hw φ hφ c)
    hprob (fun x => (hraw x).1) hq hwo hro hR (fun r => (hRaw r).1)
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_le_sum
  intro r hr
  have hco : 0 ≤ ((n : ℝ) * highFixedScoreDenominator pMinus cMass) ^ r / (r.factorial : ℝ) := by
    apply div_nonneg
    · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg n)
        (high_fixed_score_denominator_pos hpMinus hcMass).le) r
    · exact Nat.cast_nonneg _
  calc
    _ ≤ (((n : ℝ) * highFixedScoreDenominator pMinus cMass) ^ r / (r.factorial : ℝ)) *
        (((2 / (k : ℝ)) ^ d) ^ r * ∫ u, H r u
          ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))) :=
      mul_le_mul_of_nonneg_left (hRaw r).2 hco
    _ = _ := by rw [mul_pow]; ring

end NearlyMinimax
