module

public import NearlyMinimax.PilotFields


@[expose] public section

/-! Actual conditional means of two-pilot bilinear statistics. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

def pilotMean (m : W → H) (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪m w + η z.1 w, B w (m w + η z.2 w)⟫ ∂M

theorem pilotMean_sub_eq (m : W → H) (hmm : Measurable m) (hm : MemLp m 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C : ℝ} (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    {x y : Ω} (hx : MemLp (η x) 2 M) (hy : MemLp (η y) 2 M) :
    pilotMean (M := M) m η B (x, y) - (∫ w, ⟪m w, B w (m w)⟫ ∂M) =
      fluctuation (M := M) η B (fun w => B w (m w)) (fun w => B w (m w)) (x, y) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  have hBy := operatorField_memLp hmB hbound hmy hy
  have h₀ := inner_integrable hm hBm
  have h₁ := inner_integrable hx hBm
  have h₂ := inner_integrable hy hBm
  have h₃ := inner_integrable hx hBy
  have he : (fun w => ⟪m w + η x w, B w (m w + η y w)⟫) =
      (fun w => ⟪m w, B w (m w)⟫ + ⟪η x w, B w (m w)⟫ +
        ⟪η y w, B w (m w)⟫ + ⟪η x w, B w (η y w)⟫) := by
    funext w
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      hsym w (m w) (η y w), real_inner_comm (B w (m w)) (η y w)]
    ring
  have ha := integral_add ((h₀.add h₁).add h₂) h₃
  have hb := integral_add (h₀.add h₁) h₂
  have hc := integral_add h₀ h₁
  simp only [Pi.add_apply] at ha hb hc
  simp only [pilotMean, fluctuation, test, bilinear]
  rw [he, ha, hb, hc]
  ring

/-- The deterministic-centered pilot mean has its variance bound derived
from the original universal linear tests. -/
theorem pilotMean_centered_sq_le (m : W → H) (hmm : Measurable m) (hm : MemLp m 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ z, (pilotMean (M := M) m η B z - ∫ w, ⟪m w, B w (m w)⟫ ∂M) ^ 2 ∂μ.prod μ) ≤
      3 * lam * C ^ 2 * (2 * (∫ w, ‖m w‖ ^ 2 ∂M) +
        ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  have he : (fun z => (pilotMean (M := M) m η B z - ∫ w, ⟪m w, B w (m w)⟫ ∂M) ^ 2) =ᵐ[μ.prod μ]
      (fun z => fluctuation (M := M) η B (fun w => B w (m w))
        (fun w => B w (m w)) z ^ 2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (memLp_sections hη),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (memLp_sections hη)] with z hx hy
    rw [pilotMean_sub_eq m hmm hm hmη hmB hbound hsym hx hy]
  rw [integral_congr_ae he]
  apply (fluctuation_energy_le hmη hη hmB hC hlam hbound htest hBm hBm).trans
  have hv := operatorField_energy_le hmB hC hbound hmm hm
  have hcoef : 0 ≤ 3 * lam := mul_nonneg (by norm_num) hlam
  have hb := mul_le_mul_of_nonneg_left (add_le_add hv hv) hcoef
  nlinarith

end NearlyMinimax.PilotFields
