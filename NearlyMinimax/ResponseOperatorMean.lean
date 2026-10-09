module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.Moments


@[expose] public section

/-! Exact conditional quadratic-response means on the product of two error
laws. No bounded-response or higher pilot-moment assumption is used. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem product_pairScoreOperator_integral {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : E → ℝ} {Y' : F → ℝ} (hY : MemLp Y 2 μ) (hY' : MemLp Y' 2 ν)
    {f f' V : ℝ} (hm : (∫ x, Y x ∂μ) = f) (hm' : (∫ x, Y' x ∂ν) = f')
    (h2 : (∫ x, Y x ^ 2 ∂μ) = f ^ 2 + V)
    (h2' : (∫ x, Y' x ^ 2 ∂ν) = f' ^ 2 + V)
    (a b : PairVector) :
    (∫ z : E × F, ⟪a, pairScoreOperator V (Y z.1) (Y' z.2) b⟫ ∂μ.prod ν) =
      ⟪a, InnerProductSpace.rankOne ℝ (pairResponseVector f f') (pairResponseVector f f') b⟫ := by
  have hi := hY.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi' := hY'.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₀ := (hY'.integrable_sq.comp_snd μ).const_mul (a 0 * b 0)
  have h₁ := (hY.integrable_sq.comp_fst ν).const_mul (a 1 * b 1)
  have h₂ := (hi.mul_prod hi').const_mul (a 0 * b 1 + a 1 * b 0)
  have h₃ := (hi'.comp_snd μ).const_mul (a 0 * b 2 + a 2 * b 0)
  have h₄ := (hi.comp_fst ν).const_mul (a 1 * b 2 + a 2 * b 1)
  have h₅ : Integrable (fun _ : E × F => a 2 * b 2) (μ.prod ν) := integrable_const _
  have h₆ : Integrable (fun _ : E × F => V * (a 0 * b 0 + a 1 * b 1)) (μ.prod ν) :=
    integrable_const _
  have ha₀ := integral_add h₀ h₁
  have ha₁ := integral_add (h₀.add h₁) h₂
  have ha₂ := integral_add ((h₀.add h₁).add h₂) h₃
  have ha₃ := integral_add (((h₀.add h₁).add h₂).add h₃) h₄
  have ha₄ := integral_add ((((h₀.add h₁).add h₂).add h₃).add h₄) h₅
  have ha₅ := integral_sub (((((h₀.add h₁).add h₂).add h₃).add h₄).add h₅) h₆
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at ha₀ ha₁ ha₂ ha₃ ha₄ ha₅
  simp_rw [pairScoreOperator_inner_polynomial]
  rw [ha₅, ha₄, ha₃, ha₂, ha₁, ha₀]
  have hs₀ : (∫ z : E × F, Y' z.2 ^ 2 ∂μ.prod ν) = f' ^ 2 + V := by
    calc
      _ = ∫ x, Y' x ^ 2 ∂ν := by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
          integral_fun_snd (μ := μ) (ν := ν) (fun x => Y' x ^ 2)
      _ = _ := h2'
  have hs₁ : (∫ z : E × F, Y z.1 ^ 2 ∂μ.prod ν) = f ^ 2 + V := by
    calc
      _ = ∫ x, Y x ^ 2 ∂μ := by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
          integral_fun_fst (μ := μ) (ν := ν) (fun x => Y x ^ 2)
      _ = _ := h2
  simp only [integral_const_mul, integral_fun_snd, integral_fun_fst, integral_prod_mul,
    hm, hm', hs₀, hs₁, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, integral_const,
    InnerProductSpace.inner_right_rankOne_apply, pairResponseVector_inner]
  rw [real_inner_comm b (pairResponseVector f f'), pairResponseVector_inner]
  ring

theorem conditional_pairScoreOperator_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun u : ℝ => u) 2 μ) (hν : MemLp (fun u : ℝ => u) 2 ν)
    (hmμ : (∫ u : ℝ, u ∂μ) = 0) (hmν : (∫ u : ℝ, u ∂ν) = 0)
    {V : ℝ} (h2μ : (∫ u : ℝ, u ^ 2 ∂μ) = V) (h2ν : (∫ u : ℝ, u ^ 2 ∂ν) = V)
    (f f' : ℝ) (a b : PairVector) :
    (∫ z : ℝ × ℝ, ⟪a, pairScoreOperator V (f + z.1) (f' + z.2) b⟫ ∂μ.prod ν) =
      ⟪a, InnerProductSpace.rankOne ℝ (pairResponseVector f f') (pairResponseVector f f') b⟫ := by
  have hY : MemLp (fun u : ℝ => f + u) 2 μ := (memLp_const f).add hμ
  have hY' : MemLp (fun u : ℝ => f' + u) 2 ν := (memLp_const f').add hν
  apply product_pairScoreOperator_integral μ ν hY hY' _ _
    (response_second_moment_of_centered_error hμ hmμ h2μ f)
    (response_second_moment_of_centered_error hν hmν h2ν f') a b
  · rw [integral_add (integrable_const _) (hμ.integrable (by norm_num)), hmμ]
    simp
  · rw [integral_add (integrable_const _) (hν.integrable (by norm_num)), hmν]
    simp

end NearlyMinimax
