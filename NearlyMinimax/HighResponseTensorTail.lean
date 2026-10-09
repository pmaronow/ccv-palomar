module

public import NearlyMinimax.HighSeparatedScoreBounds
public import NearlyMinimax.HighUnionScore


@[expose] public section

/-! Genuine all-count Taylor bounds for arbitrary finite density-response
atom tensors and their true absolute positive reference law. Both ordinary
and fine three-point density selectors are instances of these tensors. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

section
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem responseTensor_slice_all_count_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (weights : J → ℝ) (A : ι → ι → ℝ) (pReset : J → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (y : Fin n → Fin 3) :
    |∑ e : J × HighResponseMarkIndex ι q,
      weights e.1 * highResponseMarkWeight C q A e.2 * (∏ i, pReset e.1 i) *
        highResponseProduct a V η g w φ
          (coefficientReset c (highResponseMarkAtom C q e.2).2
            (highResponseMarkAtom C q e.2).1) y| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        ∑ e : J × HighResponseMarkIndex ι q, |weights e.1 * highResponseMarkWeight C q A e.2| := by
  have he : (∑ e : J × HighResponseMarkIndex ι q,
      weights e.1 * highResponseMarkWeight C q A e.2 * (∏ i, pReset e.1 i) *
        highResponseProduct a V η g w φ
          (coefficientReset c (highResponseMarkAtom C q e.2).2
            (highResponseMarkAtom C q e.2).1) y) =
      highDensityResponseAction q C weights (fun _ => A) c
        (fun e => ∏ i, pReset e i) (fun v => highResponseProduct a V η g w φ v y) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have hh (r : HighResponseMarkIndex ι q) :
        weights e * highResponseMarkWeight C q A r * (∏ i, pReset e i) *
          highResponseProduct a V η g w φ
            (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1) y =
        (weights e*(∏ i, pReset e i)) * (highResponseMarkWeight C q A r *
          highResponseProduct a V η g w φ
            (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1) y) := by ring
    simp only [hh, ← Finset.mul_sum]
    rw [highResponseMark_action q C A c (fun v => highResponseProduct a V η g w φ v y)]
  rw [he]
  apply (high_density_response_product_abs_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
    weights (fun _ => A) pReset g w φ c hc hg hw hφ hp hReset y).trans_eq
  rw [Fintype.sum_prod_type]
  simp only [abs_mul]
  simp_rw [← Finset.mul_sum]
  rw [highResponseMark_variation q C A]
  unfold highResponsePacketCost highLocalDerivativeConstant highSeparatedDerivativeBudget
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

end

section Reference
variable {ι J Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace Z]

def responseTensorWeight (q : ℕ) (C : ℝ) (weights : J → ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × (J × HighResponseMarkIndex ι q)) : ℝ :=
  weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2

/-- Actual absolute-reference all-count raw response action is bounded by
its true variation mass and an η² Taylor factor. The variation is an
integral of the constructed signed atom weights. -/
theorem responseTensor_reference_all_count_bound {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (weights : J → ℝ) (A : Z → ι → ι → ℝ)
    (hm : Measurable (responseTensorWeight q C weights A))
    (hi : Integrable (responseTensorWeight q C weights A) (σ.prod Measure.count))
    (hpos : 0 < signedMarkMass (σ.prod Measure.count) (responseTensorWeight q C weights A))
    (pReset : Z → J → Fin n → ℝ)
    (hmReset : ∀ e i, Measurable (fun ζ => pReset ζ e i))
    (hReset : ∀ ζ e i, |pReset ζ e i| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (y : Fin n → Fin 3) :
    |highMarkedResponseAction
      (absoluteMarkLaw (σ.prod Measure.count) (responseTensorWeight q C weights A))
      (absoluteActivation (σ.prod Measure.count) (responseTensorWeight q C weights A)) a V η
      (fun e => pReset e.1 e.2.1)
      (fun e => coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
      g w φ y| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        signedMarkMass (σ.prod Measure.count) (responseTensorWeight q C weights A) := by
  let ν : Measure (Z × (J × HighResponseMarkIndex ι q)) := σ.prod Measure.count
  let W := responseTensorWeight q C weights A
  let Φ : (ι → ℝ) → ℝ := fun v => highResponseProduct a V η g w φ v y
  let O : Z × (J × HighResponseMarkIndex ι q) → ℝ := fun e => (∏ i, pReset e.1 e.2.1 i) *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
  let K := pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2
  have hResetJoint (i) : Measurable (fun e : Z × (J × HighResponseMarkIndex ι q) => pReset e.1 e.2.1 i) :=
    measurable_from_prod_countable_left (fun e => hmReset e.1 i)
  have hCoef (γ) : Measurable (fun e : Z × (J × HighResponseMarkIndex ι q) =>
      coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1 γ) :=
    (measurable_of_countable (fun e : J × HighResponseMarkIndex ι q =>
      coefficientReset c (highResponseMarkAtom C q e.2).2 (highResponseMarkAtom C q e.2).1 γ)).comp measurable_snd
  have hO : Measurable O := (Finset.measurable_fun_prod _ (fun i _ => hResetJoint i)).mul
    (highMarkedResponseProduct_measurable a V η _ hCoef g w φ y)
  have hΦ (r : HighResponseMarkIndex ι q) :
      |Φ (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1)| ≤ 1 := by
    have hb := coefficientReset_mem_ball C c (highResponseMarkAtom C q r).2
      (highResponseMarkAtom C q r).1 (responseNode_mem_unit q r.2.2) hc
      (covarianceAtom_mem_ball C hC _ _ _ _)
    apply highMarkedResponseProduct_abs_le_one a V η ha.ne' g w φ _
    intro i b
    apply hp _
    have hprof := hφ _ hb i
    change |g i+η*w i*(∑ γ, φ i γ*coefficientReset c
      (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1 γ)| ≤ ρ
    have hh : |η*w i*(∑ γ, φ i γ*coefficientReset c
        (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1 γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hη]
      have := mul_le_mul (hw i) hprof (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left this hη]
    exact (abs_add_le _ _).trans (by linarith [hg i])
  have hOb (e) : ‖O e‖ ≤ pPlus^n := by
    change |(∏ i, pReset e.1 e.2.1 i)*Φ _| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ pPlus hpPlus (hReset e.1 e.2.1))
      (hΦ e.2.2) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hWO := hi.mul_bdd hO.aestronglyMeasurable (Filter.Eventually.of_forall hOb)
  have hSlice (ζ) : |∫ e : J × HighResponseMarkIndex ι q, W (ζ,e)*O (ζ,e) ∂Measure.count| ≤
      K * ∫ e : J × HighResponseMarkIndex ι q, |W (ζ,e)| ∂Measure.count := by
    simp only [integral_count]
    simpa only [W,O,Φ,K,responseTensorWeight,mul_assoc] using
      responseTensor_slice_all_count_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        weights (A ζ) (pReset ζ) g w φ c hc hg hw hφ hp (hReset ζ) y
  unfold highMarkedResponseAction
  have he : (fun e => absoluteActivation ν W e * (∏ i, pReset e.1 e.2.1 i) *
      highResponseProduct a V η g w φ
        (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1) y) =
      (fun e => absoluteActivation ν W e * O e) := by funext e; dsimp [O,Φ]; ring
  rw [he,absoluteMarkLaw_activation_integral ν W hm hpos O,integral_prod _ hWO]
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hWO.integral_prod_left.abs (hi.abs.integral_prod_left.const_mul K) hSlice).trans_eq
  rw [integral_const_mul, ← integral_prod _ hi.abs]
  rfl

end Reference
end NearlyMinimax
