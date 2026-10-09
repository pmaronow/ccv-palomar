module

public import NearlyMinimax.HighRawScoreEnergy
public import NearlyMinimax.HighMarkedMeasurable


@[expose] public section

/-! Genuine conditional finite-response energies determine square
integrability and Fisher energy in the actual normalized sample kernel.
No joint-score integrability assumption is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def finiteResponseSquareEnergy {α : Type*} [MeasurableSpace α] (n : ℕ)
    (a V : ℝ) (F : α → ℝ) (S : ((Fin n → α) × (Fin n → Fin 3)) → ℝ)
    (x : Fin n → α) : ℝ :=
  ∑ y : Fin n → Fin 3, (∏ i, ternaryMass a (F (x i)) V (y i)) * (S (x, y)) ^ 2

theorem response_sample_square_integrable_integral {α : Type*} [MeasurableSpace α]
    (n : ℕ) (μ : Measure (Fin n → α)) [SFinite μ] (a V : ℝ) (ha : a ≠ 0)
    (F : α → ℝ) (hF : Measurable F) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (S : ((Fin n → α) × (Fin n → Fin 3)) → ℝ) (hS : Measurable S)
    (hE : Integrable (finiteResponseSquareEnergy n a V F S) μ) :
    Integrable (fun z => S z ^ 2) (μ.compProd (responseSampleIndexKernel n a V F hF)) ∧
    (∫ z, S z ^ 2 ∂μ.compProd (responseSampleIndexKernel n a V F hF)) =
      ∫ x, finiteResponseSquareEnergy n a V F S x ∂μ := by
  let _ := responseSampleIndexKernel_markov n a V F hF ha hq
  have he (x : Fin n → α) : (∫ y, ‖S (x, y) ^ 2‖ ∂responseSampleIndexKernel n a V F hF x) =
      finiteResponseSquareEnergy n a V F S x := by
    simp_rw [Real.norm_eq_abs, abs_sq]
    exact responseSampleIndexKernel_integral n a V F hF x (fun i y => hq (x i) y) _
  have hi : Integrable (fun z => S z ^ 2) (μ.compProd (responseSampleIndexKernel n a V F hF)) := by
    apply (Measure.integrable_compProd_iff (hS.pow_const 2).aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun _ => Integrable.of_finite)
    · simpa only [he] using hE
  refine ⟨hi, ?_⟩
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    responseSampleIndexKernel_integral n a V F hF x (fun i y => hq (x i) y) _)

theorem high_sample_conditional_score_integrable_integral {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (n : ℕ) (a V : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω)
    (S : ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ) (hS : Measurable S)
    (hE : Integrable (finiteResponseSquareEnergy n a V (F ω) S)
      (Measure.pi (fun _ : Fin n => highNormalizedDesignLaw (p ω)))) :
    Integrable (fun z => S z ^ 2) (highSampleIndexKernel n a V p F hp hF ω) ∧
    (∫ z, S z ^ 2 ∂highSampleIndexKernel n a V p F hp hF ω) =
      ∫ x, finiteResponseSquareEnergy n a V (F ω) S x
        ∂Measure.pi (fun _ : Fin n => highNormalizedDesignLaw (p ω)) := by
  let _ := cubeVolume_isProbability d
  have hd := high_normalized_design_probability (p ω) hp.of_uncurry_left aRaw bRaw haRaw
    (Filter.Eventually.of_forall (hraw ω))
  let _ := hd
  have hm : 0 < highRawDensityMass (p ω) := haRaw.trans_le
    (highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  have he : highSampleIndexKernel n a V p F hp hF ω =
      (Measure.pi (fun _ : Fin n => highNormalizedDesignLaw (p ω))).compProd
        (responseSampleIndexKernel n a V (F ω) hF.of_uncurry_left) := by
    rw [highSampleIndexKernel_apply]
    exact (highSample_index_density n (p ω) (F ω) hp.of_uncurry_left hF.of_uncurry_left a V hd
      (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)).symm
  rw [he]
  exact response_sample_square_integrable_integral n _ a V ha (F ω) hF.of_uncurry_left (hq ω) S hS hE

end NearlyMinimax
