module

public import NearlyMinimax.HighPatchProductExact
public import NearlyMinimax.HighSelectedScoreEnergy


@[expose] public section

/-! Actual local spatial envelopes transfer through the periodic chart
and the true normalized design likelihood, with source fixed C_sharp.
Both integrability statements are derived from the genuine Q^r envelope. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem high_raw_square_patch_integrable_bound_exact {d k r : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k)
    (R : (Fin r → Covariate d) → (Fin r → Fin 3) → ℝ)
    (hR : ∀ y, Measurable (fun x => R x y))
    (H : (Fin r → Covariate d) → ℝ)
    (hH : Integrable H (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ u, 0 ≤ H u)
    (hdom : ∀ x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy R x ≤ H (highPatchProductChart d k j x)) :
    Integrable (selectedRawSquareEnergy R)
      (Measure.pi (fun _ : Fin r => (cubeVolume d).restrict (highTorusPatch d k j))) ∧
    (∫ x, selectedRawSquareEnergy R x
      ∂Measure.pi (fun _ : Fin r => (cubeVolume d).restrict (highTorusPatch d k j))) ≤
      ((1 / (k : ℝ)) ^ d) ^ r *
        ∫ u, H u ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) := by
  let _ := cubeVolume_isProbability d
  have hrawMeas : Measurable (selectedRawSquareEnergy R) :=
    Finset.measurable_sum _ (fun y _ => (hR y).pow_const 2)
  have hraw0 (x : Fin r → Covariate d) : 0 ≤ selectedRawSquareEnergy R x :=
    Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have heval := highPatchProductChart_integrable_exact hk j H hH
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : Fin r => (cubeVolume d).restrict (highTorusPatch d k j)),
      ∀ i, x i ∈ highTorusPatch d k j :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually
      (ae_restrict_mem (highTorusPatch_measurableSet d k j)))
  have hrawI : Integrable (selectedRawSquareEnergy R)
      (Measure.pi (fun _ : Fin r => (cubeVolume d).restrict (highTorusPatch d k j))) := by
    apply heval.mono' hrawMeas.aestronglyMeasurable
    filter_upwards [hmem] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hraw0 x)]
    exact hdom x hx
  refine ⟨hrawI, ?_⟩
  calc
    _ ≤ ∫ x, H (highPatchProductChart d k j x)
        ∂Measure.pi (fun _ : Fin r => (cubeVolume d).restrict (highTorusPatch d k j)) :=
      integral_mono_ae hrawI heval (hmem.mono (fun x hx => hdom x hx))
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using highPatchProductChart_integral_le_exact hk j H hH hH0

theorem high_normalized_selected_spatial_energy_bound_exact {d k r : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (m pMinus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (p : Covariate d → ℝ) (hpMeas : Measurable p) (q : Covariate d → Fin 3 → ℝ)
    (hqMeas : ∀ y, Measurable (fun x => q x y))
    (R : (Fin r → Covariate d) → (Fin r → Fin 3) → ℝ) (hR : ∀ y, Measurable (fun x => R x y))
    (hprob : IsProbabilityMeasure ((cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ highTorusPatch d k j, pMinus ≤ p x)
    (hq : ∀ x ∈ highTorusPatch d k j, ∀ y, cMass ≤ q x y)
    (H : (Fin r → Covariate d) → ℝ)
    (hH : Integrable H (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ u, 0 ≤ H u)
    (hdom : ∀ x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy R x ≤ H (highPatchProductChart d k j x)) :
    Integrable (selectedConditionalScoreEnergy p q R)
      (Measure.pi (fun _ : Fin r => ((cubeVolume d).withDensity
        (fun x => ENNReal.ofReal (p x / m))).restrict (highTorusPatch d k j))) ∧
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ : Fin r => ((cubeVolume d).withDensity
        (fun x => ENNReal.ofReal (p x / m))).restrict (highTorusPatch d k j))) ≤
      (highFixedScoreDenominator pMinus cMass * (1 / (k : ℝ)) ^ d) ^ r *
        ∫ u, H u ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) := by
  let _ := cubeVolume_isProbability d
  have hraw := high_raw_square_patch_integrable_bound_exact hk j R hR H hH hH0 hdom
  have hs := normalized_selected_score_energy_integrable_bound (cubeVolume d)
    (highTorusPatch d k j) (highTorusPatch_measurableSet d k j) m pMinus cMass hpMinus hcMass hm
    p hpMeas q hqMeas R hR hprob hp hq hraw.1
  refine ⟨hs.1, ?_⟩
  apply hs.2.trans
  calc
    _ ≤ highFixedScoreDenominator pMinus cMass ^ r *
        (((1 / (k : ℝ)) ^ d) ^ r * ∫ u, H u
          ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))) := by
      simpa only [Fintype.card_fin] using mul_le_mul_of_nonneg_left hraw.2
        (pow_nonneg (high_fixed_score_denominator_pos hpMinus hcMass).le r)
    _ = _ := by rw [mul_pow]; ring

end NearlyMinimax
