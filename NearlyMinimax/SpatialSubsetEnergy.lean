module

public import NearlyMinimax.SpatialSubsetIntegral
public import Mathlib.Data.Finset.Powerset


@[expose] public section

/-! Actual square-integrability and finite subset-sum energy bounds on Q^k. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem finite_pi_reindex_integrable {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (e : I ≃ J) (f : (J → E) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : J => μ))) :
    Integrable (fun U : I → E => f (fun j => U (e.symm j))) (Measure.pi (fun _ : I => μ)) := by
  have hp := measurePreserving_piCongrLeft (fun _ : J => μ) e
  have he (U : I → E) : (Equiv.piCongrLeft (fun _ : J => E) e) U =
      fun j => U (e.symm j) := by
    funext j
    simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  have h := hp.integrable_comp_of_integrable hf
  simpa only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft, he] using h

theorem spatial_subset_square_integrable_enumerated {d k : ℕ} (s : Finset (Fin k))
    (f : (Fin s.card → Covariate d) → ℝ)
    (hf : Integrable (fun V => f V ^ 2) (fullSpatialPatchDesign d s.card)) :
    Integrable (fun U : Fin k → Covariate d => f (spatialSubsetConfiguration s U) ^ 2)
      (fullSpatialPatchDesign d k) := by
  let e : s ≃ Fin s.card := (Fintype.equivFin s).trans (finCongr (Fintype.card_coe s))
  have hi := finite_pi_reindex_integrable (volume.restrict (spatialPatchBox d)) e
    (fun V => f V ^ 2) hf
  have h := finite_pi_subset_integrable (volume.restrict (spatialPatchBox d)) s
    (fun V : s → Covariate d => f (fun j => V (e.symm j)) ^ 2) hi
  exact h

theorem finite_sum_square_integral_le {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ) (K : ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ)
    (hK : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ K) :
    (∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ≤ (s.card : ℝ) ^ 2 * K := by
  classical
  have hb (x : X) : (∑ i ∈ s, f i x) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : I => (1 : ℝ)) (fun i => f i x)
  have hu : Integrable (fun x => (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2) μ :=
    (integrable_finsetSum s hi).const_mul _
  have hl : Integrable (fun x => (∑ i ∈ s, f i x) ^ 2) μ := by
    apply hu.mono' ((Finset.measurable_fun_sum s hm).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_sq]
      exact hb x)
  have h := integral_mono hl hu hb
  rw [integral_const_mul, integral_finsetSum _ hi] at h
  apply h.trans
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hK) (Nat.cast_nonneg s.card)
  simpa only [Finset.sum_const, nsmul_eq_mul, sq, ← mul_assoc] using hh

/-- This is the exact binomial and unused-coordinate factor in the paper's
subset lift; each selected kernel is integrated over its genuine Q^r law. -/
theorem spatial_subset_sum_square_integral_le {d k r : ℕ}
    (f : (s : Finset (Fin k)) → (Fin s.card → Covariate d) → ℝ) (K : ℝ)
    (hm : ∀ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r, Measurable (f s))
    (hi : ∀ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r,
      Integrable (fun V => f s V ^ 2) (fullSpatialPatchDesign d s.card))
    (hK : ∀ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r,
      (∫ V, f s V ^ 2 ∂fullSpatialPatchDesign d s.card) ≤ K) :
    (∫ U, (∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r,
      f s (spatialSubsetConfiguration s U)) ^ 2 ∂fullSpatialPatchDesign d k) ≤
      (k.choose r : ℝ) ^ 2 * (2 : ℝ) ^ (d * (k - r)) * K := by
  classical
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d k)
    ((Finset.univ : Finset (Fin k)).powersetCard r)
    (fun s U => f s (spatialSubsetConfiguration s U)) ((2 : ℝ) ^ (d * (k - r)) * K)
    (fun s hs => (hm s hs).comp (spatialSubsetConfiguration_measurable s))
    (fun s hs => spatial_subset_square_integrable_enumerated s (f s) (hi s hs))
    (fun s hs => by
      rw [spatial_subset_square_integral_enumerated]
      have hc := (Finset.mem_powersetCard.mp hs).2
      have hv : (2 : ℝ) ^ (d * (k - s.card)) = (2 : ℝ) ^ (d * (k - r)) := by rw [hc]
      rw [hv]
      exact mul_le_mul_of_nonneg_left (hK s hs) (by positivity))
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← mul_assoc] using h

end NearlyMinimax
