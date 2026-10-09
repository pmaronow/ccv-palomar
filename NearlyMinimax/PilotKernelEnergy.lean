module

public import NearlyMinimax.PilotFields


@[expose] public section

/-! Product-pilot kernel energies. Independence is implemented by the actual
product measure; the second moment bound is derived from the two pilot L²
energies rather than supplied as a kernel-moment assumption. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem operator_inner_sq_le (A : H →L[ℝ] H) (u v : H) :
    ⟪u, A v⟫ ^ 2 ≤ ‖A‖ ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := (abs_real_inner_le_norm u (A v)).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg u))
  calc
    _ ≤ (‖u‖ * (‖A‖ * ‖v‖)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by ring

theorem product_operator_kernel_sq_integrable (A : H →L[ℝ] H)
    {f g : Ω → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z : Ω × Ω => ⟪f z.1, A (g z.2)⟫ ^ 2) (μ.prod μ) := by
  have hm : AEStronglyMeasurable
      (fun z : Ω × Ω => ⟪f z.1, A (g z.2)⟫ ^ 2) (μ.prod μ) :=
    (hf.aestronglyMeasurable.comp_fst.inner
      (A.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable.comp_snd)).pow 2
  have hi := (hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq).const_mul (‖A‖ ^ 2)
  apply hi.mono' hm
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_assoc] using operator_inner_sq_le A (f z.1) (g z.2))

theorem product_operator_kernel_energy_le (A : H →L[ℝ] H)
    {f g : Ω → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ z : Ω × Ω, ⟪f z.1, A (g z.2)⟫ ^ 2 ∂μ.prod μ) ≤
      ‖A‖ ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  calc
    _ ≤ ∫ z : Ω × Ω, ‖A‖ ^ 2 * (‖f z.1‖ ^ 2 * ‖g z.2‖ ^ 2) ∂μ.prod μ := by
      apply integral_mono (product_operator_kernel_sq_integrable A hf hg)
        ((hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq).const_mul _)
      intro z
      simpa only [mul_assoc] using operator_inner_sq_le A (f z.1) (g z.2)
    _ = _ := by
      rw [integral_const_mul, integral_prod_mul (fun x : Ω => ‖f x‖ ^ 2) (fun x : Ω => ‖g x‖ ^ 2)]
      ring

theorem product_operator_kernel_energy_le_uniform (A : H →L[ℝ] H)
    {f g : Ω → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {L : ℝ} (hL : 0 ≤ L)
    (hEf : (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ L) (hEg : (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ L) :
    (∫ z : Ω × Ω, ⟪f z.1, A (g z.2)⟫ ^ 2 ∂μ.prod μ) ≤ ‖A‖ ^ 2 * L ^ 2 := by
  apply (product_operator_kernel_energy_le A hf hg).trans
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hEf (sq_nonneg ‖A‖))
    (integral_nonneg (μ := μ) (fun x : Ω => sq_nonneg ‖g x‖))
  have h2 := mul_le_mul_of_nonneg_left hEg (mul_nonneg (sq_nonneg ‖A‖) hL)
  nlinarith

end NearlyMinimax.PilotFields
