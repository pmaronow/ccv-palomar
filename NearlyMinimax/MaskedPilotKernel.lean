module

public import NearlyMinimax.WeightedPilotEnergy


@[expose] public section

/-! Actual masked bilinear kernels inherit joint L² integrability from pilot
second moments and a weighted response-operator second moment. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

def maskedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫

theorem maskedPilotKernel_measurable {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) : Measurable (maskedPilotKernel c A q) := by
  exact (hmq.comp measurable_snd).mul
    ((hmc.comp (measurable_fst.fst.prodMk measurable_snd)).inner
      (hmA.comp (measurable_snd.prodMk
        (hmc.comp (measurable_fst.snd.prodMk measurable_snd)))))

theorem maskedPilotKernel_sq_eq {c : Ω → W → H} {A : W → H →L[ℝ] H}
    {q : W → ℝ} (hq : ∀ w, q w ^ 2 = q w) (z : (Ω × Ω) × W) :
    maskedPilotKernel c A q z ^ 2 = weightedPilotKernel c A q z := by
  simp only [maskedPilotKernel, weightedPilotKernel, mul_pow, hq]

theorem maskedPilotKernel_memLp {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    MemLp (maskedPilotKernel c A q) 2 ((μ.prod μ).prod ν) := by
  apply (memLp_two_iff_integrable_sq
    (maskedPilotKernel_measurable hmc hmA hmq).aestronglyMeasurable).2
  simp_rw [maskedPilotKernel_sq_eq hq]
  exact weightedPilotKernel_integrable hmc hmA hmq
    (Filter.Eventually.of_forall (fun w => (hq w).symm ▸ sq_nonneg (q w))) hA hc hL hE

theorem maskedPilotKernel_energy_le {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    (∫ z, maskedPilotKernel c A q z ^ 2 ∂(μ.prod μ).prod ν) ≤
      L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  simp_rw [maskedPilotKernel_sq_eq hq]
  exact weightedPilotKernel_energy_le hmc hmA hmq
    (Filter.Eventually.of_forall (fun w => (hq w).symm ▸ sq_nonneg (q w))) hA hc hL hE

end NearlyMinimax.PilotFields
