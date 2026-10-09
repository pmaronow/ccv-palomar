module

public import NearlyMinimax.PilotFields


@[expose] public section

/-! Uniform section bounds imply genuine joint pilot L² integrability. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

theorem memLp_joint_of_uniform_section_energy {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ)
    {R : ℝ} (hR : 0 ≤ R) (hE : ∀ᵐ w ∂M, (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ R) :
    MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M) := by
  apply (memLp_two_iff_integrable_sq_norm hmη.aestronglyMeasurable).2
  have hm : AEStronglyMeasurable (fun z : Ω × W => ‖η z.1 z.2‖ ^ 2) (μ.prod M) :=
    hmη.aestronglyMeasurable.norm.pow 2
  apply (integrable_prod_iff' hm).2
  constructor
  · exact hη.mono (fun _ hw => hw.norm.integrable_sq)
  · apply (integrable_const R).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hE] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Function.comp_def, Prod.swap_prod_mk, norm_pow,
      Real.norm_eq_abs, sq_abs] using hw

theorem joint_energy_le_of_uniform_sections {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ)
    {R : ℝ} (hR : 0 ≤ R) (hE : ∀ᵐ w ∂M, (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ R) :
    (∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) ≤ R * M.real Set.univ := by
  have hi := (memLp_joint_of_uniform_section_energy hmη hη hR hE).norm.integrable_sq
  rw [integral_prod_symm _ hi]
  apply (integral_mono_ae hi.integral_prod_right (integrable_const R) hE).trans_eq
  simp [integral_const, mul_comm]

end NearlyMinimax.PilotFields
