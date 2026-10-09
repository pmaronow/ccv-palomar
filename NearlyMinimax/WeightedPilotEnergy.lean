module

public import NearlyMinimax.PilotKernelEnergy


@[expose] public section

/-! Weighted observation-kernel energy averaged over two independent pilots.
The Fubini and integrability obligations are derived from section L² bounds. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

def weightedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫ ^ 2

theorem weightedPilotKernel_measurable {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) : Measurable (weightedPilotKernel c A q) := by
  have hi : Measurable (fun z : (Ω × Ω) × W =>
      ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫) :=
    (hmc.comp (measurable_fst.fst.prodMk measurable_snd)).inner
      (hmA.comp (measurable_snd.prodMk
        (hmc.comp (measurable_fst.snd.prodMk measurable_snd))))
  exact (hmq.comp measurable_snd).mul (hi.pow_const 2)

theorem weightedPilotKernel_section_integrable {c : Ω → W → H}
    {A : W → H →L[ℝ] H} {q : W → ℝ} {w : W}
    (hc : MemLp (fun x => c x w) 2 μ) :
    Integrable (fun z : Ω × Ω => weightedPilotKernel c A q (z, w)) (μ.prod μ) :=
  (product_operator_kernel_sq_integrable (A w) hc hc).const_mul (q w)

theorem weightedPilotKernel_section_energy_le {c : Ω → W → H}
    {A : W → H →L[ℝ] H} {q : W → ℝ} {w : W}
    (hc : MemLp (fun x => c x w) 2 μ) {L : ℝ} (hL : 0 ≤ L)
    (hE : (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) (hq : 0 ≤ q w) :
    (∫ z : Ω × Ω, weightedPilotKernel c A q (z, w) ∂μ.prod μ) ≤
      L ^ 2 * (q w * ‖A w‖ ^ 2) := by
  change (∫ z : Ω × Ω, q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2 ∂μ.prod μ) ≤ _
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (product_operator_kernel_energy_le_uniform (A w) hc hc hL hE hE) hq
  nlinarith

theorem weightedPilotKernel_integrable {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ᵐ w ∂ν, 0 ≤ q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    Integrable (weightedPilotKernel c A q) ((μ.prod μ).prod ν) := by
  have hm : AEStronglyMeasurable (weightedPilotKernel c A q) ((μ.prod μ).prod ν) :=
    (weightedPilotKernel_measurable hmc hmA hmq).aestronglyMeasurable
  apply (integrable_prod_iff' hm).2
  constructor
  · exact hc.mono (fun _ hw => weightedPilotKernel_section_integrable hw)
  · apply (hA.const_mul (L ^ 2)).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hc, hE, hq] with w hcw hEw hqw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    change (∫ z : Ω × Ω, ‖weightedPilotKernel c A q (z, w)‖ ∂μ.prod μ) ≤ _
    have hn : (fun z : Ω × Ω => ‖weightedPilotKernel c A q (z, w)‖) =
        (fun z : Ω × Ω => weightedPilotKernel c A q (z, w)) := by
      funext z
      change ‖q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2‖ =
        q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hqw (sq_nonneg _))]
    rw [hn]
    exact weightedPilotKernel_section_energy_le hcw hL hEw hqw

theorem weightedPilotKernel_energy_le {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ᵐ w ∂ν, 0 ≤ q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    (∫ z, weightedPilotKernel c A q z ∂(μ.prod μ).prod ν) ≤
      L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  have hi := weightedPilotKernel_integrable hmc hmA hmq hq hA hc hL hE
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_mono_ae hi.integral_prod_right (hA.const_mul _)
  filter_upwards [hc, hE, hq] with w hcw hEw hqw
  exact weightedPilotKernel_section_energy_le hcw hL hEw hqw

end NearlyMinimax.PilotFields
