module

public import NearlyMinimax.PairLocalization


@[expose] public section

/-! Symmetrized, weighted, order-two pair statistics. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [MeasurableSingletonClass I]
variable {μ : Measure E} [IsProbabilityMeasure μ]

def weightedSymmetrization (weight : ℝ) (G : E × E → ℝ) (z : E × E) : ℝ :=
  weight / 4 * (G z + G z.swap)

theorem weightedSymmetrization_measurable (weight : ℝ) {G : E × E → ℝ}
    (hmG : Measurable G) : Measurable (weightedSymmetrization weight G) :=
  (hmG.add (hmG.comp measurable_swap)).const_mul _

theorem weightedSymmetrization_symmetric (weight : ℝ) (G : E × E → ℝ) (x y : E) :
    weightedSymmetrization weight G (x, y) = weightedSymmetrization weight G (y, x) := by
  simp only [weightedSymmetrization, Prod.swap_prod_mk, add_comm]

theorem weightedSymmetrization_memLp (weight : ℝ) {G : E × E → ℝ}
    (hG : MemLp G 2 (μ.prod μ)) : MemLp (weightedSymmetrization weight G) 2 (μ.prod μ) :=
  (hG.add (hG.comp_measurePreserving Measure.measurePreserving_swap)).const_mul _

theorem weightedSymmetrization_mean (weight : ℝ) {G : E × E → ℝ}
    (hG : MemLp G 2 (μ.prod μ)) :
    (∫ z, weightedSymmetrization weight G z ∂μ.prod μ) =
      weight / 2 * ∫ z, G z ∂μ.prod μ := by
  have h₁ := hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₂ := (hG.comp_measurePreserving Measure.measurePreserving_swap).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have ha := integral_add h₁ h₂
  simp only [Function.comp_def] at ha
  simp only [weightedSymmetrization]
  rw [integral_const_mul, ha, integral_prod_swap G]
  ring

theorem weightedSymmetrization_energy_le (weight : ℝ) {G : E × E → ℝ}
    (hG : MemLp G 2 (μ.prod μ)) :
    (∫ z, weightedSymmetrization weight G z ^ 2 ∂μ.prod μ) ≤
      weight ^ 2 / 4 * ∫ z, G z ^ 2 ∂μ.prod μ := by
  have h₁ := hG.integrable_sq
  have h₂ := (hG.comp_measurePreserving Measure.measurePreserving_swap).integrable_sq
  calc
    _ ≤ ∫ z : E × E, weight ^ 2 / 8 * (G z ^ 2 + G z.swap ^ 2) ∂μ.prod μ := by
      apply integral_mono (weightedSymmetrization_memLp weight hG).integrable_sq
        ((h₁.add h₂).const_mul _)
      intro z
      have hs : (G z + G z.swap) ^ 2 ≤ 2 * (G z ^ 2 + G z.swap ^ 2) := by
        nlinarith [sq_nonneg (G z - G z.swap)]
      have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ weight ^ 2 / 16)
      dsimp [weightedSymmetrization]
      nlinarith
    _ = _ := by
      have ha := integral_add h₁ h₂
      simp only [Pi.add_apply, Function.comp_def] at ha
      rw [integral_const_mul, ha, integral_prod_swap (fun z => G z ^ 2)]
      ring

theorem weightedSymmetrization_supported (weight : ℝ) (label : E → I)
    {G : E × E → ℝ} (hsupport : ∀ x y, label x ≠ label y → G (x, y) = 0) :
    ∀ x y, label x ≠ label y → weightedSymmetrization weight G (x, y) = 0 := by
  intro x y hxy
  simp only [weightedSymmetrization, Prod.swap_prod_mk, hsupport x y hxy,
    hsupport y x (Ne.symm hxy), add_zero, mul_zero]

theorem weighted_pair_centered_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {n : ℕ} (hn : 2 ≤ n)
    (X : Fin n → Ω → E) (hind : ProbabilityTheory.iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ)
    (label : E → I) (hlabel : Measurable label)
    {G : E × E → ℝ} (hmG : Measurable G) (hG : MemLp G 2 (μ.prod μ))
    (hsupport : ∀ x y, label x ≠ label y → G (x, y) = 0)
    {weight cap P : ℝ} (hweight : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) (hP : weight * cap ≤ P) :
    (∫ x, (pairAverage n (weightedSymmetrization weight G) (fun i => X i x) -
      weight / 2 * ∫ z, G z ∂μ.prod μ) ^ 2 ∂ν) ≤
      (P / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) *
        (weight * ∫ z, G z ^ 2 ∂μ.prod μ) := by
  have hv := partition_pairAverage_centered_sq_le hn X hind hX label hlabel
    (weightedSymmetrization_measurable weight hmG) (weightedSymmetrization_memLp weight hG)
    (weightedSymmetrization_symmetric weight G) (weightedSymmetrization_supported weight label hsupport)
    hmass
  rw [weightedSymmetrization_mean weight hG] at hv
  apply hv.trans
  have hcoef : 0 ≤ 4 / (n : ℝ) * cap + 2 / ((n : ℝ) * (n - 1 : ℕ)) := by positivity
  apply (mul_le_mul_of_nonneg_left (weightedSymmetrization_energy_le weight hG) hcoef).trans
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm0 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have henergy : 0 ≤ ∫ z, G z ^ 2 ∂μ.prod μ := integral_nonneg (fun _ => sq_nonneg _)
  have hscale : (4 / (n : ℝ) * cap + 2 / ((n : ℝ) * (n - 1 : ℕ))) * (weight ^ 2 / 4) =
      (weight * cap / (n : ℝ) + weight / (2 * (n : ℝ) * (n - 1 : ℕ))) * weight := by
    field_simp
    <;> ring
  rw [← mul_assoc, hscale]
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (add_le_add_right (div_le_div_of_nonneg_right hP hn0.le)
        (weight / (2 * (n : ℝ) * (n - 1 : ℕ)))) hweight.le) henergy
  nlinarith

end NearlyMinimax.PairUStatistic
