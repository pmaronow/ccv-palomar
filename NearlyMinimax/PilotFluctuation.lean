module

public import NearlyMinimax.LocalizationL2


@[expose] public section

/-! Independent pilot fluctuation estimates. These estimates integrate the
actual product law of the two pilots; no bilinear variance estimate is assumed. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFluctuation

set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem bilinear_sq_integrable {η : Ω → H} (hη : MemLp η 2 μ)
    (B : H →L[ℝ] H) :
    Integrable (fun z : Ω × Ω => ⟪η z.1, B (η z.2)⟫ ^ 2) (μ.prod μ) := by
  have hm : AEStronglyMeasurable
      (fun z : Ω × Ω => ⟪η z.1, B (η z.2)⟫ ^ 2) (μ.prod μ) :=
    (hη.aestronglyMeasurable.comp_fst.inner
      (B.continuous.comp_aestronglyMeasurable hη.aestronglyMeasurable.comp_snd)).pow 2
  have hb := (hη.norm.integrable_sq.mul_prod hη.norm.integrable_sq).const_mul (‖B‖ ^ 2)
  apply hb.mono' hm
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    ⟪η z.1, B (η z.2)⟫ ^ 2 ≤ (‖η z.1‖ * ‖B (η z.2)‖) ^ 2 := by
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (η z.1) (B (η z.2))) 2
    _ ≤ (‖η z.1‖ * (‖B‖ * ‖η z.2‖)) ^ 2 := by
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)) 2
    _ = ‖B‖ ^ 2 * (‖η z.1‖ ^ 2 * ‖η z.2‖ ^ 2) := by ring

/-- The universal linear-test bound controls the bilinear term of two
independent pilots, with only one total second moment. -/
theorem bilinear_sq_bound {η : Ω → H} (hη : MemLp η 2 μ)
    (B : H →L[ℝ] H) {lam : ℝ} (hlam : 0 ≤ lam)
    (htest : ∀ v : H, (∫ x, ⟪η x, v⟫ ^ 2 ∂μ) ≤ lam * ‖v‖ ^ 2) :
    (∫ z : Ω × Ω, ⟪η z.1, B (η z.2)⟫ ^ 2 ∂μ.prod μ) ≤
      lam * ‖B‖ ^ 2 * ∫ x, ‖η x‖ ^ 2 ∂μ := by
  rw [integral_prod_symm _ (bilinear_sq_integrable hη B)]
  calc
    _ ≤ ∫ y, lam * ‖B‖ ^ 2 * ‖η y‖ ^ 2 ∂μ := by
      apply integral_mono
        (bilinear_sq_integrable hη B).integral_prod_right
        (hη.norm.integrable_sq.const_mul (lam * ‖B‖ ^ 2))
      intro y
      calc
        (∫ x, ⟪η x, B (η y)⟫ ^ 2 ∂μ) ≤ lam * ‖B (η y)‖ ^ 2 := htest _
        _ ≤ lam * (‖B‖ * ‖η y‖) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2) hlam
        _ = lam * ‖B‖ ^ 2 * ‖η y‖ ^ 2 := by ring
    _ = _ := integral_const_mul _ _

theorem three_square_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

theorem bilinear_memLp_two {η : Ω → H} (hη : MemLp η 2 μ)
    (B : H →L[ℝ] H) :
    MemLp (fun z : Ω × Ω => ⟪η z.1, B (η z.2)⟫) 2 (μ.prod μ) := by
  exact (memLp_two_iff_integrable_sq
    (hη.aestronglyMeasurable.comp_fst.inner
      (B.continuous.comp_aestronglyMeasurable hη.aestronglyMeasurable.comp_snd))).2
    (bilinear_sq_integrable hη B)

theorem bilinear_mean_zero {η : Ω → H} (hη : MemLp η 2 μ)
    (B : H →L[ℝ] H)
    (hcenter : ∀ v : H, (∫ x, ⟪η x, v⟫ ∂μ) = 0) :
    (∫ z : Ω × Ω, ⟪η z.1, B (η z.2)⟫ ∂μ.prod μ) = 0 := by
  rw [integral_prod_symm _ ((bilinear_memLp_two hη B).integrable (by norm_num))]
  simp only [hcenter, integral_zero]

/-- The centered expansion of a bilinear pilot functional. -/
def fluctuation (η : Ω → H) (B : H →L[ℝ] H) (v₁ v₂ : H) (z : Ω × Ω) : ℝ :=
  ⟪η z.1, v₁⟫ + ⟪η z.2, v₂⟫ + ⟪η z.1, B (η z.2)⟫

theorem fluctuation_sq_integrable {η : Ω → H} (hη : MemLp η 2 μ)
    (B : H →L[ℝ] H) (v₁ v₂ : H) :
    Integrable (fun z => fluctuation η B v₁ v₂ z ^ 2) (μ.prod μ) := by
  have h₁ : MemLp (fun z : Ω × Ω => ⟪η z.1, v₁⟫) 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq (hη.aestronglyMeasurable.comp_fst.inner
      aestronglyMeasurable_const)).2
    exact (hη.inner_const (𝕜 := ℝ) v₁).integrable_sq.comp_fst μ
  have h₂ : MemLp (fun z : Ω × Ω => ⟪η z.2, v₂⟫) 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq (hη.aestronglyMeasurable.comp_snd.inner
      aestronglyMeasurable_const)).2
    exact (hη.inner_const (𝕜 := ℝ) v₂).integrable_sq.comp_snd μ
  exact ((h₁.add h₂).add (bilinear_memLp_two hη B)).integrable_sq

theorem fluctuation_mean_zero {η : Ω → H} (hη : MemLp η 2 μ)
    (B : H →L[ℝ] H) (v₁ v₂ : H)
    (hcenter : ∀ v : H, (∫ x, ⟪η x, v⟫ ∂μ) = 0) :
    (∫ z, fluctuation η B v₁ v₂ z ∂μ.prod μ) = 0 := by
  have h₁ : Integrable (fun z : Ω × Ω => ⟪η z.1, v₁⟫) (μ.prod μ) :=
    ((hη.inner_const (𝕜 := ℝ) v₁).integrable (by norm_num)).comp_fst μ
  have h₂ : Integrable (fun z : Ω × Ω => ⟪η z.2, v₂⟫) (μ.prod μ) :=
    ((hη.inner_const (𝕜 := ℝ) v₂).integrable (by norm_num)).comp_snd μ
  have h₃ := (bilinear_memLp_two hη B).integrable (by norm_num)
  have ha := integral_add (h₁.add h₂) h₃
  have hb := integral_add h₁ h₂
  simp only [Pi.add_apply] at ha hb
  simp only [fluctuation]
  rw [ha, hb,
    integral_fun_fst (μ := μ) (ν := μ) (fun x => ⟪η x, v₁⟫),
    integral_fun_snd (μ := μ) (ν := μ) (fun x => ⟪η x, v₂⟫), hcenter, hcenter, bilinear_mean_zero hη B hcenter]
  simp

theorem fluctuation_sq_bound {η : Ω → H} (hη : MemLp η 2 μ)
    (B : H →L[ℝ] H) (v₁ v₂ : H) {lam : ℝ} (hlam : 0 ≤ lam)
    (htest : ∀ v : H, (∫ x, ⟪η x, v⟫ ^ 2 ∂μ) ≤ lam * ‖v‖ ^ 2) :
    (∫ z, fluctuation η B v₁ v₂ z ^ 2 ∂μ.prod μ) ≤
      3 * lam * (‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 + ‖B‖ ^ 2 * ∫ x, ‖η x‖ ^ 2 ∂μ) := by
  have h₁ := (hη.inner_const (𝕜 := ℝ) v₁).integrable_sq.comp_fst μ
  have h₂ := (hη.inner_const (𝕜 := ℝ) v₂).integrable_sq.comp_snd μ
  have h₃ := bilinear_sq_integrable hη B
  calc
    _ ≤ ∫ z : Ω × Ω,
        3 * (⟪η z.1, v₁⟫ ^ 2 + ⟪η z.2, v₂⟫ ^ 2 +
          ⟪η z.1, B (η z.2)⟫ ^ 2) ∂μ.prod μ := by
      exact integral_mono (fluctuation_sq_integrable hη B v₁ v₂)
        (((h₁.add h₂).add h₃).const_mul 3) (fun z => three_square_le _ _ _)
    _ = 3 * ((∫ x, ⟪η x, v₁⟫ ^ 2 ∂μ) + (∫ x, ⟪η x, v₂⟫ ^ 2 ∂μ) +
        (∫ z : Ω × Ω, ⟪η z.1, B (η z.2)⟫ ^ 2 ∂μ.prod μ)) := by
      have ha := integral_add (h₁.add h₂) h₃
      have hb := integral_add h₁ h₂
      simp only [Pi.add_apply] at ha hb
      rw [integral_const_mul, ha, hb,
        integral_fun_fst (μ := μ) (ν := μ) (fun x => ⟪η x, v₁⟫ ^ 2),
        integral_fun_snd (μ := μ) (ν := μ) (fun x => ⟪η x, v₂⟫ ^ 2)]
      simp
    _ ≤ 3 * (lam * ‖v₁‖ ^ 2 + lam * ‖v₂‖ ^ 2 +
        lam * ‖B‖ ^ 2 * ∫ x, ‖η x‖ ^ 2 ∂μ) := by
      gcongr
      · exact htest v₁
      · exact htest v₂
      · exact bilinear_sq_bound hη B hlam htest
    _ = _ := by ring

end NearlyMinimax.PilotFluctuation
