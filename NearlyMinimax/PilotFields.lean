module

public import NearlyMinimax.PilotFluctuation


@[expose] public section

/-! Pilot fields remain ordinary jointly measurable functions. The scalar
test and independent-pilot bounds below do not assume measurability of a
random map into an L² quotient space. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

theorem toLp_norm_sq {f : W → H} (hf : MemLp f 2 M) :
    ‖hf.toLp f‖ ^ 2 = ∫ w, ‖f w‖ ^ 2 ∂M := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with w hw
  rw [hw, real_inner_self_eq_norm_sq]

theorem toLp_inner {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ w, ⟪f w, g w⟫ ∂M := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  rw [hfw, hgw]

theorem inner_integral_sq_le {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M) :
    (∫ w, ⟪f w, g w⟫ ∂M) ^ 2 ≤
      (∫ w, ‖f w‖ ^ 2 ∂M) * (∫ w, ‖g w‖ ^ 2 ∂M) := by
  rw [← toLp_inner hf hg, ← toLp_norm_sq hf, ← toLp_norm_sq hg]
  calc
    _ ≤ (‖hf.toLp f‖ * ‖hg.toLp g‖) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)) 2
    _ = _ := by ring

theorem inner_integrable {f g : W → H} (hf : MemLp f 2 M) (hg : MemLp g 2 M) :
    Integrable (fun w => ⟪f w, g w⟫) M := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  rw [hfw, hgw]

def test (η : Ω → W → H) (v : W → H) (x : Ω) : ℝ :=
  ∫ w, ⟪η x w, v w⟫ ∂M

theorem memLp_sections {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M)) :
    ∀ᵐ x ∂μ, MemLp (η x) 2 M := by
  filter_upwards [hη.aestronglyMeasurable.prodMk_left,
    hη.norm.integrable_sq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

theorem test_aestronglyMeasurable {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    AEStronglyMeasurable (test (M := M) η v) μ := by
  have hm : AEStronglyMeasurable
      (fun z : Ω × W => ⟪η z.1 z.2, v z.2⟫) (μ.prod M) :=
    hη.aestronglyMeasurable.inner hv.aestronglyMeasurable.comp_snd
  exact hm.integral_prod_right'

theorem test_sq_integrable {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    Integrable (fun x => test (M := M) η v x ^ 2) μ := by
  have hi := hη.norm.integrable_sq.integral_prod_left.mul_const
    (∫ w, ‖v w‖ ^ 2 ∂M)
  apply hi.mono' ((test_aestronglyMeasurable hη hv).pow 2)
  filter_upwards [memLp_sections hη] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact inner_integral_sq_le hx hv

theorem test_memLp_two {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {v : W → H} (hv : MemLp v 2 M) :
    MemLp (test (M := M) η v) 2 μ :=
  (memLp_two_iff_integrable_sq (test_aestronglyMeasurable hη hv)).2
    (test_sq_integrable hη hv)

/-- Pointwise mean centering implies centering against every deterministic
L² test, with the Fubini integrability obligation proved. -/
theorem test_mean_zero [CompleteSpace H] {η : Ω → W → H}
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {v : W → H} (hv : MemLp v 2 M) :
    (∫ x, test (M := M) η v x ∂μ) = 0 := by
  have hcomp : MemLp (fun z : Ω × W => v z.2) 2 (μ.prod M) :=
    hv.comp_measurePreserving measurePreserving_snd
  have hi := inner_integrable hη hcomp
  change (∫ x, ∫ w, ⟪η x w, v w⟫ ∂M ∂μ) = 0
  rw [← integral_prod _ hi, integral_prod_symm _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards [hcenter, hη.aestronglyMeasurable.prodMk_right,
    hη.norm.integrable_sq.prod_left_ae] with w hw hm hisq
  have hηw : MemLp (fun x => η x w) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hm).2 hisq
  calc
    (∫ x, ⟪η x w, v w⟫ ∂μ) = ∫ x, ⟪v w, η x w⟫ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => real_inner_comm _ _)
    _ = ⟪v w, ∫ x, η x w ∂μ⟫ := integral_inner (hηw.integrable (by norm_num)) _
    _ = 0 := by rw [hw]; simp

section OperatorField
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

def bilinear (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪η z.1 w, B w (η z.2 w)⟫ ∂M

theorem bilinear_measurable {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2)) :
    Measurable (bilinear (M := M) η B) := by
  have hm : Measurable (fun z : (Ω × Ω) × W =>
      ⟪η z.1.1 z.2, B z.2 (η z.1.2 z.2)⟫) := by
    apply Measurable.inner
    · exact hmη.comp (measurable_fst.fst.prodMk measurable_snd)
    · exact hmB.comp (measurable_snd.prodMk
        (hmη.comp (measurable_fst.snd.prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem operatorField_memLp {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C : ℝ} (hbound : ∀ w, ‖B w‖ ≤ C)
    {f : W → H} (hmf : Measurable f) (hf : MemLp f 2 M) :
    MemLp (fun w => B w (f w)) 2 M := by
  apply hf.of_le_mul (c := C)
    (hmB.comp (measurable_id.prodMk hmf)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w =>
    ((B w).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _)))

theorem operatorField_energy_le {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ w, ‖B w‖ ≤ C)
    {f : W → H} (hmf : Measurable f) (hf : MemLp f 2 M) :
    (∫ w, ‖B w (f w)‖ ^ 2 ∂M) ≤ C ^ 2 * ∫ w, ‖f w‖ ^ 2 ∂M := by
  rw [← integral_const_mul]
  apply integral_mono (operatorField_memLp hmB hbound hmf hf).norm.integrable_sq
    (hf.norm.integrable_sq.const_mul (C ^ 2))
  intro w
  calc
    ‖B w (f w)‖ ^ 2 ≤ (C * ‖f w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (((B w).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg _))) 2
    _ = C ^ 2 * ‖f w‖ ^ 2 := by ring

theorem bilinear_section_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {y : Ω} (hy : MemLp (η y) 2 M) :
    (∫ x, bilinear (M := M) η B (x, y) ^ 2 ∂μ) ≤
      lam * C ^ 2 * ∫ w, ‖η y w‖ ^ 2 ∂M := by
  have hm : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  have hv := operatorField_memLp hmB hbound hm hy
  have hb := (htest (fun w => B w (η y w)) hv).trans
    (mul_le_mul_of_nonneg_left (operatorField_energy_le hmB hC hbound hm hy) hlam)
  simpa only [test, bilinear, mul_assoc] using hb

theorem bilinear_sq_integrable {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    Integrable (fun z => bilinear (M := M) η B z ^ 2) (μ.prod μ) := by
  have hmZ : AEStronglyMeasurable
      (fun z : Ω × Ω => bilinear (M := M) η B z ^ 2) (μ.prod μ) :=
    (bilinear_measurable (M := M) hmη hmB).aestronglyMeasurable.pow 2
  apply (integrable_prod_iff' hmZ).2
  constructor
  · filter_upwards [memLp_sections hη] with y hy
    have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
    exact test_sq_integrable hη (operatorField_memLp hmB hbound hmy hy)
  · have hi := hη.norm.integrable_sq.integral_prod_left.const_mul (lam * C ^ 2)
    apply hi.mono' hmZ.norm.prod_swap.integral_prod_right'
    filter_upwards [memLp_sections hη] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp only [norm_pow, Real.norm_eq_abs, sq_abs]
    exact bilinear_section_energy_le hmη hmB hC hlam hbound htest hy

/-- The integrated test estimate supplies the bilinear fluctuation bound
for the actual product of two jointly measurable pilot fields. -/
theorem bilinear_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ) ≤
      lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M := by
  have hZ := bilinear_sq_integrable hmη hη hmB hC hlam hbound htest
  rw [integral_prod_symm _ hZ]
  calc
    _ ≤ ∫ y, lam * C ^ 2 * (∫ w, ‖η y w‖ ^ 2 ∂M) ∂μ := by
      apply integral_mono_ae hZ.integral_prod_right
        (hη.norm.integrable_sq.integral_prod_left.const_mul (lam * C ^ 2))
      filter_upwards [memLp_sections hη] with y hy
      exact bilinear_section_energy_le hmη hmB hC hlam hbound htest hy
    _ = _ := by
      rw [integral_const_mul, integral_prod _ hη.norm.integrable_sq]

theorem bilinear_memLp_two {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    MemLp (bilinear (M := M) η B) 2 (μ.prod μ) :=
  (memLp_two_iff_integrable_sq
    (bilinear_measurable (M := M) hmη hmB).aestronglyMeasurable).2
    (bilinear_sq_integrable hmη hη hmB hC hlam hbound htest)

theorem bilinear_mean_zero [CompleteSpace H] {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, bilinear (M := M) η B z ∂μ.prod μ) = 0 := by
  rw [integral_prod_symm _
    ((bilinear_memLp_two hmη hη hmB hC hlam hbound htest).integrable (by norm_num))]
  apply integral_eq_zero_of_ae
  filter_upwards [memLp_sections hη] with y hy
  have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  exact test_mean_zero hη hcenter (operatorField_memLp hmB hbound hmy hy)

def fluctuation (η : Ω → W → H) (B : W → H →L[ℝ] H)
    (v₁ v₂ : W → H) (z : Ω × Ω) : ℝ :=
  test (M := M) η v₁ z.1 + test (M := M) η v₂ z.2 + bilinear (M := M) η B z

theorem fluctuation_memLp_two {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    MemLp (fluctuation (M := M) η B v₁ v₂) 2 (μ.prod μ) := by
  have h₁ : MemLp (fun z : Ω × Ω => test (M := M) η v₁ z.1) 2 (μ.prod μ) :=
    (test_memLp_two hη hv₁).comp_measurePreserving measurePreserving_fst
  have h₂ : MemLp (fun z : Ω × Ω => test (M := M) η v₂ z.2) 2 (μ.prod μ) :=
    (test_memLp_two hη hv₂).comp_measurePreserving measurePreserving_snd
  exact (h₁.add h₂).add (bilinear_memLp_two hmη hη hmB hC hlam hbound htest)

theorem fluctuation_energy_le {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H}
    (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    (∫ z, fluctuation (M := M) η B v₁ v₂ z ^ 2 ∂μ.prod μ) ≤
      3 * lam * ((∫ w, ‖v₁ w‖ ^ 2 ∂M) + (∫ w, ‖v₂ w‖ ^ 2 ∂M) +
        C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  have h₁ := (test_sq_integrable hη hv₁).comp_fst μ
  have h₂ := (test_sq_integrable hη hv₂).comp_snd μ
  have h₃ := bilinear_sq_integrable hmη hη hmB hC hlam hbound htest
  calc
    _ ≤ ∫ z : Ω × Ω, 3 * (test (M := M) η v₁ z.1 ^ 2 +
        test (M := M) η v₂ z.2 ^ 2 + bilinear (M := M) η B z ^ 2) ∂μ.prod μ := by
      exact integral_mono
        (fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hv₁ hv₂).integrable_sq
        (((h₁.add h₂).add h₃).const_mul 3)
        (fun _ => PilotFluctuation.three_square_le _ _ _)
    _ = 3 * ((∫ x, test (M := M) η v₁ x ^ 2 ∂μ) +
        (∫ x, test (M := M) η v₂ x ^ 2 ∂μ) +
        (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ)) := by
      have ha := integral_add (h₁.add h₂) h₃
      have hb := integral_add h₁ h₂
      simp only [Pi.add_apply] at ha hb
      rw [integral_const_mul, ha, hb,
        integral_fun_fst (μ := μ) (ν := μ) (fun x => test (M := M) η v₁ x ^ 2),
        integral_fun_snd (μ := μ) (ν := μ) (fun x => test (M := M) η v₂ x ^ 2)]
      simp
    _ ≤ 3 * (lam * (∫ w, ‖v₁ w‖ ^ 2 ∂M) + lam * (∫ w, ‖v₂ w‖ ^ 2 ∂M) +
        lam * C ^ 2 * ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
      gcongr
      · exact htest v₁ hv₁
      · exact htest v₂ hv₂
      · exact bilinear_energy_le hmη hη hmB hC hlam hbound htest
    _ = _ := by ring

end OperatorField

end NearlyMinimax.PilotFields
