module

public import NearlyMinimax.Risk


@[expose] public section

/-! Risk averaging for independent pilots and evaluation observations.
The loss remains an extended-real integral throughout. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem two_stage_mean_squared_bound {P X : Type*}
    [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure P) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : P × X → ℝ) (L b : P → ℝ) (hmT : Measurable T) (hmL : Measurable L)
    (hb : Integrable b μ) (hb0 : ∀ᵐ p ∂μ, 0 ≤ b p)
    {a d c : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hconditional : ∀ᵐ p ∂μ,
      (∫⁻ x, ENNReal.ofReal ((T (p, x) - L p) ^ 2) ∂ν) ≤ ENNReal.ofReal (a * b p))
    (hmean : (∫⁻ p, ENNReal.ofReal ((L p - c) ^ 2) ∂μ) ≤ ENNReal.ofReal d) :
    (∫⁻ z, ENNReal.ofReal ((T z - c) ^ 2) ∂μ.prod ν) ≤
      ENNReal.ofReal (2 * a * (∫ p, b p ∂μ) + 2 * d) := by
  let f : P × X → ℝ≥0∞ := fun z => ENNReal.ofReal ((T z - L z.1) ^ 2)
  let g : P × X → ℝ≥0∞ := fun z => ENNReal.ofReal ((L z.1 - c) ^ 2)
  have hf : Measurable f := ((hmT.sub (hmL.comp measurable_fst)).pow_const 2).ennreal_ofReal
  have hg : Measurable g := (((hmL.comp measurable_fst).sub measurable_const).pow_const 2).ennreal_ofReal
  have heval : (∫⁻ z, f z ∂μ.prod ν) ≤ ENNReal.ofReal (a * ∫ p, b p ∂μ) := by
    rw [lintegral_prod _ hf.aemeasurable]
    apply (lintegral_mono_ae hconditional).trans
    have hab0 : ∀ᵐ p ∂μ, 0 ≤ a * b p := hb0.mono (fun _ hp => mul_nonneg ha hp)
    rw [← ofReal_integral_eq_lintegral_ofReal (hb.const_mul a) hab0, integral_const_mul]
  have hmean' : (∫⁻ z, g z ∂μ.prod ν) ≤ ENNReal.ofReal d := by
    rw [lintegral_prod _ hg.aemeasurable]
    simp only [g, lintegral_const, measure_univ, mul_one]
    exact hmean
  have hbudget : 0 ≤ a * ∫ p, b p ∂μ :=
    mul_nonneg ha (integral_nonneg_of_ae hb0)
  calc
    _ ≤ ∫⁻ z, (2 : ℝ≥0∞) * f z + 2 * g z ∂μ.prod ν := by
      apply lintegral_mono
      intro z
      have hs : (T z - c) ^ 2 ≤ 2 * (T z - L z.1) ^ 2 + 2 * (L z.1 - c) ^ 2 := by
        nlinarith [sq_nonneg ((T z - L z.1) - (L z.1 - c))]
      have he := ENNReal.ofReal_le_ofReal hs
      simpa only [f, g, ENNReal.ofReal_add (by positivity : 0 ≤ 2 * (T z - L z.1) ^ 2)
        (by positivity : 0 ≤ 2 * (L z.1 - c) ^ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using he
    _ = 2 * (∫⁻ z, f z ∂μ.prod ν) + 2 * (∫⁻ z, g z ∂μ.prod ν) := by
      have hf2 : Measurable (fun z : P × X => (2 : ℝ≥0∞) * f z) := measurable_const.mul hf
      rw [lintegral_add_left hf2, lintegral_const_mul _ hf, lintegral_const_mul _ hg]
    _ ≤ 2 * ENNReal.ofReal (a * ∫ p, b p ∂μ) + 2 * ENNReal.ofReal d := by
      gcongr
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hbudget) (mul_nonneg (by norm_num) hd)]
      congr 1
      ring

end NearlyMinimax
