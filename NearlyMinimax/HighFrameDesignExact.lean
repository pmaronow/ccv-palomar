module

public import NearlyMinimax.HighFrameDesignEnergy
public import NearlyMinimax.HighMarkedSpatialExact


@[expose] public section

/-! Exact original-scale finite marked score energy, using the genuine
periodic chart Jacobian without a wrapping multiplicity constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
section
variable {E : Type*} [MeasurableSpace E]

theorem high_frame_complete_design_spatial_series_exact (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (π : HighWindowLabels d k → Measure E) [∀ j, SFinite (π j)]
    (activation : HighWindowLabels d k → E → ℝ)
    (hAct : ∀ j, Measurable (activation j)) (hActI : ∀ j, Integrable (activation j) (π j))
    (a V η pMinus pPlus cMass : ℝ) (ha : a ≠ 0) (hpMinus : 0 < pMinus)
    (hpPlus : 0 ≤ pPlus) (hcMass : 0 < cMass)
    (p : Covariate d → ℝ) (hp : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    (pReset : HighWindowLabels d k → E → Covariate d → ℝ)
    (hReset : ∀ j, Measurable (Function.uncurry (pReset j)))
    (hBound : ∀ j e x, |pReset j e x| ≤ pPlus)
    (hOutside : ∀ j e x, x ∉ highTorusPatch d k j → pReset j e x = p x)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (hq : ∀ x y, cMass ≤ ternaryMass a (highFrameField d k η (fun l => highFramePolynomial (c l)) x) V y)
    (hqReset : ∀ j e x y, 0 ≤ highMarkedResponseMass a V η
      (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
      (fun x => highLocalFrameFeature k j x) (cReset j e) x y)
    (hDensity : ∀ j (x : Fin n → Covariate d),
      (∫ e, activation j e * ∏ i, pReset j e (x i) ∂π j) = 0)
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ j r, Integrable (H j r) (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ j r u, 0 ≤ H j r u)
    (hdom : ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r (π j) (activation j) a V η p (pReset j)
        (cReset j) (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
          (fun x => highLocalFrameFeature k j x) (c j)) x ≤ H j r (highPatchProductChart d k j x)) :
    let F := highFrameField d k η (fun l => highFramePolynomial (c l))
    let hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
    let S := highFrameFullMarkedScore d k D n π activation a V η p pReset cReset c
    Integrable (fun z => S z ^ 2) ((Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)).compProd
      (responseSampleIndexKernel n a V F hF)) ∧
    (∫ z, S z ^ 2 ∂(Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)).compProd
      (responseSampleIndexKernel n a V F hF)) ≤
      (3 ^ d : ℕ) * ∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
        ((n : ℝ) * highFixedScoreDenominator pMinus cMass * (1 / (k : ℝ)) ^ d) ^ r /
          (r.factorial : ℝ) * ∫ u, H j r u
            ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) := by
  let F := highFrameField d k η (fun l => highFramePolynomial (c l))
  have hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
  let S := highFrameFullMarkedScore d k D n π activation a V η p pReset cReset c
  let μ := Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)
  let _ := high_normalized_design_probability p hp pMinus pPlus hpMinus (Filter.Eventually.of_forall hraw)
  let Eglobal := finiteResponseSquareEnergy n a V F S
  let Elocal (j : HighWindowLabels d k) := highMarkedSampleConditionalEnergy n (π j) (activation j)
    a V η p (pReset j) (cReset j) (highLocalFieldWithout d k D η c j)
      (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) (c j)
  have hqLocal (j : HighWindowLabels d k) (x : Covariate d) (y : Fin 3) :
      cMass ≤ highMarkedResponseMass a V η (highLocalFieldWithout d k D η c j)
        (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) (c j) x y := by
    unfold highMarkedResponseMass
    rw [← highFrameField_local_decomposition d k D hk η c j x]
    exact hq x y
  have hlocal (j : HighWindowLabels d k) := high_marked_original_design_spatial_series_exact hk j n
    (π j) (activation j) (hAct j) a V η ha pMinus pPlus cMass hpMinus hcMass p hp hraw
    (pReset j) (hReset j) (cReset j) (hcReset j)
    (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
    (highLocalFieldWithout_continuous d k D η c j).measurable
    (highPeriodicTensor_contDiff d k j).continuous.measurable
    (fun x => highLocalFrameFeature k j x) (highLocalFrameFeature_measurable k j) (c j)
    (hqLocal j) (fun x hx => by
      by_contra h
      exact hx (highPeriodicTensor_supported_patch d k j h))
    (hOutside j) (H j) (hH j) (hH0 j) (hdom j)
  have hSm : Measurable S := highFrameFullMarkedScore_measurable d k D n π activation hAct
    a V η p hp pReset hReset cReset hcReset c
  have hEm : Measurable Eglobal := by
    apply Finset.measurable_sum
    intro y hy
    exact (Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V _ (hF.comp (measurable_pi_apply i)) (y i))).mul
        ((hSm.comp (measurable_id.prodMk measurable_const)).pow_const 2)
  have hEn (x : Fin n → Covariate d) : 0 ≤ Eglobal x :=
    Finset.sum_nonneg (fun y _ => mul_nonneg
      (Finset.prod_nonneg (fun i _ => hcMass.le.trans (hq (x i) (y i)))) (sq_nonneg _))
  have hpoint (x : Fin n → Covariate d) : Eglobal x ≤ (3 ^ d : ℕ) * ∑ j, Elocal j x := by
    have he := highFrameMarkedScore_energy_bound d k D n hk π activation hActI a V η pPlus ha hpPlus
      (p ∘ x) (fun j e => pReset j e ∘ x)
      (fun j i => (hReset j).comp (measurable_id.prodMk measurable_const))
      (fun j e i => hBound j e (x i)) cReset hcReset c x
      (fun i => (hpMinus.trans_le (hraw (x i)).1).ne')
      (fun i y => hcMass.trans_le (hq (x i) y))
      (fun j e i y => hqReset j e (x i) y) (fun j => hDensity j x)
    rw [ternary_index_product_integral] at he
    have hloc (j : HighWindowLabels d k) :
        (∫ y, highFrameMarkedScore d k D n π activation a V η (p ∘ x)
          (fun j e => pReset j e ∘ x) cReset c x j y ^ 2
          ∂Measure.pi (fun i => ternaryIndexMeasure a (F (x i)) V ha
            (fun y => (hcMass.trans_le (hq (x i) y)).le))) = Elocal j x := by
      have hreg := highFrameField_coefficientRegression d k D n hk η c j x
      change coefficientRegression η (highLocalFieldWithout d k D η c j ∘ x)
        (highPeriodicTensor d k j ∘ x) ((fun x => highLocalFrameFeature k j x) ∘ x) (c j) =
          (fun i => F (x i)) at hreg
      have hs := high_marked_sample_energy_integral n (π j) (activation j) a V η ha p (pReset j)
        (cReset j) (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
          (fun x => highLocalFrameFeature k j x) (c j) x
            (fun x y => hcMass.trans_le (hqLocal j x y))
      rw [ternary_index_product_integral] at hs
      rw [hreg] at hs
      rw [ternary_index_product_integral]
      exact hs
    dsimp only [F] at hloc
    simp_rw [hloc] at he
    exact he
  have hu : Integrable (fun x => (3 ^ d : ℕ) * ∑ j, Elocal j x) μ :=
    (integrable_finsetSum _ (fun j _ => (hlocal j).1)).const_mul _
  have hEI : Integrable Eglobal μ := by
    apply hu.mono' hEm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hEn x)]
      exact hpoint x)
  have hs := response_sample_square_integrable_integral n μ a V ha F hF
    (fun x y => hcMass.le.trans (hq x y)) S hSm hEI
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  calc
    _ ≤ ∫ x, (3 ^ d : ℕ) * ∑ j, Elocal j x ∂μ := integral_mono hEI hu hpoint
    _ = (3 ^ d : ℕ) * ∑ j, ∫ x, Elocal j x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hlocal j).1)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hlocal j).2)) (Nat.cast_nonneg _)

end
end NearlyMinimax
