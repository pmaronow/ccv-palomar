module

public import NearlyMinimax.PilotMean


@[expose] public section

/-! Centered independent pilot fields give the exact deterministic population
mean, as well as genuine L² integrability of the bilinear pilot mean. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

theorem fluctuation_mean_zero {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    (∫ z, fluctuation (M := M) η B v₁ v₂ z ∂μ.prod μ) = 0 := by
  have h₁ := (test_memLp_two hη hv₁).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₂ := (test_memLp_two hη hv₂).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₃ := (bilinear_memLp_two hmη hη hmB hC hlam hbound htest).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have ha := integral_add ((h₁.comp_fst μ).add (h₂.comp_snd μ)) h₃
  have hb := integral_add (h₁.comp_fst μ) (h₂.comp_snd μ)
  simp only [Pi.add_apply] at ha hb
  change (∫ z : Ω × Ω, test (M := M) η v₁ z.1 + test (M := M) η v₂ z.2 +
    bilinear (M := M) η B z ∂μ.prod μ) = 0
  rw [ha, hb, integral_fun_fst, integral_fun_snd,
    test_mean_zero hη hcenter hv₁, test_mean_zero hη hcenter hv₂,
    bilinear_mean_zero hmη hη hcenter hmB hC hlam hbound htest]
  simp

theorem pilotMean_eq_fluctuation_ae (m : W → H) (hmm : Measurable m) (hm : MemLp m 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C : ℝ} (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫) :
    pilotMean (M := M) m η B =ᵐ[μ.prod μ]
      (fun z => fluctuation (M := M) η B (fun w => B w (m w))
        (fun w => B w (m w)) z + ∫ w, ⟪m w, B w (m w)⟫ ∂M) := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (memLp_sections hη),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (memLp_sections hη)] with z hx hy
  have he := pilotMean_sub_eq m hmm hm hmη hmB hbound hsym hx hy
  linarith

theorem pilotMean_memLp_two (m : W → H) (hmm : Measurable m) (hm : MemLp m 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    MemLp (pilotMean (M := M) m η B) 2 (μ.prod μ) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  exact ((fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hBm hBm).add
    (memLp_const (∫ w, ⟪m w, B w (m w)⟫ ∂M))).ae_eq
      (pilotMean_eq_fluctuation_ae m hmm hm hmη hη hmB hbound hsym).symm

theorem pilotMean_mean_eq (m : W → H) (hmm : Measurable m) (hm : MemLp m 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, pilotMean (M := M) m η B z ∂μ.prod μ) = ∫ w, ⟪m w, B w (m w)⟫ ∂M := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  rw [integral_congr_ae (pilotMean_eq_fluctuation_ae m hmm hm hmη hη hmB hbound hsym)]
  rw [integral_add ((fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hBm hBm).integrable
    (by norm_num)) (integrable_const _),
    fluctuation_mean_zero hmη hη hcenter hmB hC hlam hbound htest hBm hBm]
  simp

end NearlyMinimax.PilotFields
