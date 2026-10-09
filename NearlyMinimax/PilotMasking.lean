module

public import NearlyMinimax.MaskedPilotKernel


@[expose] public section

/-! Pilot fields need L² bounds only where the pair mask is nonzero. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

def restrictPilotField (c : Ω → W → H) (q : W → ℝ) (x : Ω) (w : W) : H :=
  if q w = 0 then 0 else c x w

theorem restrictPilotField_measurable {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) :
    Measurable (fun z : Ω × W => restrictPilotField c q z.1 z.2) :=
  Measurable.ite ((hmq.comp measurable_snd) (measurableSet_singleton 0))
    measurable_const hmc

theorem restrictPilotField_memLp {c : Ω → W → H} {q : W → ℝ}
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ) :
    ∀ᵐ w ∂ν, MemLp (fun x => restrictPilotField c q x w) 2 μ := by
  filter_upwards [hc] with w hw
  by_cases hq : q w = 0
  · simpa [restrictPilotField, hq] using
      (memLp_const (μ := μ) (p := 2) (0 : H))
  · simpa [restrictPilotField, hq] using hw hq

theorem restrictPilotField_energy_le {c : Ω → W → H} {q : W → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    ∀ᵐ w ∂ν, (∫ x, ‖restrictPilotField c q x w‖ ^ 2 ∂μ) ≤ L := by
  filter_upwards [hE] with w hw
  by_cases hq : q w = 0
  · simpa [restrictPilotField, hq] using hL
  · simpa [restrictPilotField, hq] using hw hq

theorem maskedPilotKernel_restrict_eq (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) : maskedPilotKernel (restrictPilotField c q) A q = maskedPilotKernel c A q := by
  funext z
  by_cases hq : q z.2 = 0 <;> simp [maskedPilotKernel, restrictPilotField, hq]

theorem maskedPilotKernel_memLp_of_supported_sections {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    MemLp (maskedPilotKernel c A q) 2 ((μ.prod μ).prod ν) := by
  rw [← maskedPilotKernel_restrict_eq c A q]
  exact maskedPilotKernel_memLp (restrictPilotField_measurable hmc hmq) hmA hmq hq hA
    (restrictPilotField_memLp hc) hL (restrictPilotField_energy_le hL hE)

theorem maskedPilotKernel_energy_le_of_supported_sections {c : Ω → W → H}
    (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q) (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hL : 0 ≤ L) (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    (∫ z, maskedPilotKernel c A q z ^ 2 ∂(μ.prod μ).prod ν) ≤
      L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  rw [← maskedPilotKernel_restrict_eq c A q]
  exact maskedPilotKernel_energy_le (restrictPilotField_measurable hmc hmq) hmA hmq hq hA
    (restrictPilotField_memLp hc) hL (restrictPilotField_energy_le hL hE)

end NearlyMinimax.PilotFields
