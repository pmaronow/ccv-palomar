module

public import NearlyMinimax.HighCenteredRowUnion
public import NearlyMinimax.HighScoreOrthogonality


@[expose] public section

/-! The actual full local signed-generator score. A genuine mark law acts
on the reset density and coefficient vector. The variance derivative occurs
exactly once, after the ordinary and fine-pair row actions are combined. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

def highMarkedResponseAction {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∫ e, activation e * (∏ i, pReset e i) *
    highResponseProduct a V η g w φ (cReset e) y ∂π

def highMarkedLocalScore {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)

theorem highMarkedResponseProduct_measurable {n : ℕ} (a V η : ℝ)
    (cReset : E → ι → ℝ) (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (y : Fin n → Fin 3) :
    Measurable (fun e => highResponseProduct a V η g w φ (cReset e) y) := by
  unfold highResponseProduct
  apply Finset.measurable_fun_prod
  intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  fun_prop

theorem highMarkedResponseProduct_abs_le_one {n : ℕ} (a V η : ℝ) (ha : a ≠ 0)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (v : ι → ℝ)
    (hp : ∀ i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ v i) V b)
    (y : Fin n → Fin 3) : |highResponseProduct a V η g w φ v y| ≤ 1 := by
  unfold highResponseProduct
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_of_nonneg (hp i (y i))]
    exact ternary_mass_le_one a _ V ha (hp i) (y i)

/-- Integrability follows from the actual integrable activation, Borel
legal resets, and normalized nonnegative response masses. -/
theorem highMarkedResponseAction_integrable {n : ℕ} (π : Measure E)
    (activation : E → ℝ) (hAct : Integrable activation π)
    (a V η : ℝ) (ha : a ≠ 0) (pPlus : ℝ) (hpPlus : 0 ≤ pPlus)
    (pReset : E → Fin n → ℝ) (hReset : ∀ i, Measurable (fun e => pReset e i))
    (hBound : ∀ e i, |pReset e i| ≤ pPlus) (cReset : E → ι → ℝ)
    (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hp : ∀ e i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ (cReset e) i) V b)
    (y : Fin n → Fin 3) :
    Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π := by
  have hDensity := hAct.mul_bdd
    (Finset.measurable_fun_prod _ (fun i _ => hReset i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using
        finite_density_product_abs_bound (pReset e) pPlus hpPlus (hBound e)))
  exact hDensity.mul_bdd (highMarkedResponseProduct_measurable a V η cReset hc g w φ y).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using
        highMarkedResponseProduct_abs_le_one a V η ha g w φ (cReset e) (hp e) y))

/-- Response normalization identifies the actual total action with the
conditional density action, rather than assuming score centering. -/
theorem highMarkedResponseAction_sum {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (ha : a ≠ 0) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hInt : ∀ y, Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π) :
    (∑ y : Fin n → Fin 3, highMarkedResponseAction π activation a V η pReset cReset g w φ y) =
      ∫ e, activation e * ∏ i, pReset e i ∂π := by
  unfold highMarkedResponseAction
  rw [← integral_finsetSum Finset.univ (fun y _ => hInt y)]
  simp_rw [← Finset.mul_sum, high_response_product_normalized a V η ha, mul_one]

/-- The full marked score is conditionally centered whenever the actual
signed density action vanishes. For the source row union this primitive
comes from each row's proved conditional zero-mass rule. -/
theorem highMarkedLocalScore_centered {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (ha : a ≠ 0) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hInt : ∀ y, Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π)
    (hDensity : (∫ e, activation e * ∏ i, pReset e i ∂π) = 0) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V
        ha (fun b => (hp i b).le))) = 0 := by
  rw [ternary_index_product_integral]
  change (∑ y, highResponseProduct a V η g w φ c y *
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y) = 0
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have he (y : Fin n → Fin 3) :
      highResponseProduct a V η g w φ c y *
        highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
        η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 *
          highResponseVarianceTerm a V η g w φ c y i) / (∏ i, p i) := by
    have hL : highResponseProduct a V η g w φ c y ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
    unfold highMarkedLocalScore
    field_simp [hB, hL]
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    highMarkedResponseAction_sum π activation a V η ha pReset cReset g w φ hInt,
    hDensity, ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, high_response_variance_term_sum_zero,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_div]

theorem highMarkedLocalScore_depends_on_support {n : ℕ} (π : Measure E)
    (activation : E → ℝ) (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c y' := by
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have hLy : highResponseProduct a V η g w φ c y ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
  have hLy' : highResponseProduct a V η g w φ c y' ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y' i)))
  have hfirst : highMarkedResponseAction π activation a V η pReset cReset g w φ y /
      highResponseProduct a V η g w φ c y =
    highMarkedResponseAction π activation a V η pReset cReset g w φ y' /
      highResponseProduct a V η g w φ c y' := by
    unfold highMarkedResponseAction
    rw [← integral_div, ← integral_div]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro e
    simp only [mul_div_assoc]
    rw [high_response_ratio_depends_on_support a V η g w φ c (cReset e) S hw y y' hyy hp]
  have hvar :
      (∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
        highResponseProduct a V η g w φ c y =
      (∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y' i) /
        highResponseProduct a V η g w φ c y' := by
    simp_rw [Finset.sum_div, mul_div_assoc,
      high_response_variance_ratio a V η g w φ c y _ (fun i => hp i (y i)),
      high_response_variance_ratio a V η g w φ c y' _ (fun i => hp i (y' i))]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · rw [hyy i hi]
    · simp [hw i hi]
  have hrep (z : Fin n → Fin 3) (hL : highResponseProduct a V η g w φ c z ≠ 0) :
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c z =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ z /
        highResponseProduct a V η g w φ c z) / (∏ i, p i) -
      η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c z i) /
        highResponseProduct a V η g w φ c z) := by
    unfold highMarkedLocalScore
    field_simp [hB, hL]
  rw [hrep y hLy, hrep y' hLy', hfirst, hvar]

end

section RowUnion
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  {E : J → Type*} [∀ j, MeasurableSpace (E j)]

/-- The genuine complete local first action is the sum of its actual row
signed-measure actions. The unique corrective branch has zero activation. -/
theorem highCenteredRowUnion_response_action {n : ℕ}
    (π : (j : J) → Measure (E j)) (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (activation : (j : J) → E j → ℝ)
    (hAct : ∀ j, Measurable (activation j)) (hInt : ∀ j, Integrable (activation j) (π j))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus)
    (pReset : (Sigma E) ⊕ Unit → Fin n → ℝ)
    (hReset : ∀ i, Measurable (fun e => pReset e i))
    (hBound : ∀ e i, |pReset e i| ≤ pPlus)
    (cReset : (Sigma E) ⊕ Unit → ι → ℝ)
    (hc : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hp : ∀ e i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ (cReset e) i) V b)
    (y : Fin n → Fin 3) :
    highMarkedResponseAction (highCenteredRowUnionLaw π B δ)
      (highCenteredRowUnionActivation B activation δ) a V η pReset cReset g w φ y =
      ∑ j, ∫ᵛ e, (∏ i, pReset (Sum.inl ⟨j,e⟩) i) *
        highResponseProduct a V η g w φ (cReset (Sum.inl ⟨j,e⟩)) y
        ∂<•(π j).withDensityᵥ (activation j) := by
  unfold highMarkedResponseAction
  simp_rw [mul_assoc]
  apply highCenteredRowUnion_signed_action π B hB hTotal activation hAct hInt δ hδ hδ1
    (fun e => (∏ i, pReset e i) * highResponseProduct a V η g w φ (cReset e) y)
    ((Finset.measurable_fun_prod _ (fun i _ => hReset i)).mul
      (highMarkedResponseProduct_measurable a V η cReset hc g w φ y)) (pPlus^n)
  intro e
  rw [Real.norm_eq_abs, abs_mul]
  have hd := finite_density_product_abs_bound (pReset e) pPlus hpPlus (hBound e)
  have hr := highMarkedResponseProduct_abs_le_one a V η ha g w φ (cReset e) (hp e) y
  calc
    _ ≤ pPlus^n * 1 := mul_le_mul hd hr (abs_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- Conditional density annihilation of the complete union is derived from
the actual row signed integrals, and is the centering input above. -/
theorem highCenteredRowUnion_density_annihilation {n : ℕ}
    (π : (j : J) → Measure (E j)) (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (activation : (j : J) → E j → ℝ)
    (hAct : ∀ j, Measurable (activation j)) (hInt : ∀ j, Integrable (activation j) (π j))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (pPlus : ℝ) (hpPlus : 0 ≤ pPlus)
    (pReset : (Sigma E) ⊕ Unit → Fin n → ℝ)
    (hReset : ∀ i, Measurable (fun e => pReset e i))
    (hBound : ∀ e i, |pReset e i| ≤ pPlus)
    (hZero : ∀ j, (∫ᵛ e, ∏ i, pReset (Sum.inl ⟨j,e⟩) i
      ∂<•(π j).withDensityᵥ (activation j)) = 0) :
    (∫ e, highCenteredRowUnionActivation B activation δ e * (∏ i, pReset e i)
      ∂highCenteredRowUnionLaw π B δ) = 0 := by
  rw [highCenteredRowUnion_signed_action π B hB hTotal activation hAct hInt δ hδ hδ1
    (fun e => ∏ i, pReset e i) (Finset.measurable_fun_prod _ (fun i _ => hReset i))
    (pPlus^n) (fun e => by
      simpa only [Real.norm_eq_abs] using
        finite_density_product_abs_bound (pReset e) pPlus hpPlus (hBound e))]
  simp only [hZero, Finset.sum_const_zero]

end RowUnion
end NearlyMinimax
