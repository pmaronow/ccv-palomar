module

public import NearlyMinimax.HighLocalScores
public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.NeighborScoreEnergy
public import NearlyMinimax.ActualSeparatedPacket


@[expose] public section

/-! Locality and disjoint-patch orthogonality of the actual high-regime
density-response score. Density resets need not be independent: conditioning
on the design leaves independent response coordinates, and the outside
response likelihood cancels from each true signed-packet ratio. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section FinitePacket
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

theorem high_response_ratio_depends_on_support {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c v : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highResponseProduct a V η g w φ v y / highResponseProduct a V η g w φ c y =
      highResponseProduct a V η g w φ v y' / highResponseProduct a V η g w φ c y' := by
  let outside (z : Fin n → Fin 3) : ℝ :=
    ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (z i)
  let inside (z : Fin n → Fin 3) (u : ι → ℝ) : ℝ :=
    ∏ i ∈ S, ternaryMass a (coefficientRegression η g w φ u i) V (z i)
  have hfactor (z : Fin n → Fin 3) (u : ι → ℝ) :
      highResponseProduct a V η g w φ u z = outside z * inside z u := by
    unfold highResponseProduct
    rw [← Finset.prod_sdiff (Finset.subset_univ S)]
    dsimp [outside, inside]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2]
  have hout (z : Fin n → Fin 3) : outside z ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    simpa [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2] using hp i (z i)
  have hin (z : Fin n → Fin 3) : inside z c ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (z i)))
  have hs (u : ι → ℝ) : inside y u = inside y' u := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hyy i hi]
  rw [hfactor y v, hfactor y c, hfactor y' v, hfactor y' c, hs v, hs c]
  field_simp [hout y, hout y', hin y']

theorem high_response_variance_ratio {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : Fin n → Fin 3) (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (coefficientRegression η g w φ c k) V (y k)) :
    highResponseVarianceTerm a V η g w φ c y i / highResponseProduct a V η g w φ c y =
      ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i) := by
  unfold highResponseVarianceTerm highResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (coefficientRegression η g w φ c k) V (y k)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun k _ => hp k))
  exact mul_div_mul_right _ _ hrest

theorem high_local_score_ratio_representation {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ k, 0 < ternaryMass a (coefficientRegression η g w φ c k) V (y k)) :
    highLocalScore q C a V η weights A p pReset g w φ c y =
      (∑ e, (weights e * (∏ i, pReset e i) / (∏ i, p i)) *
        responseMatrixAction q C (A e) c (fun v =>
          highResponseProduct a V η g w φ v y / highResponseProduct a V η g w φ c y)) -
      η ^ 2 * ∑ i, (w i) ^ 2 *
        (ternaryVarianceDerivative a (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i)) := by
  have hL : highResponseProduct a V η g w φ c y ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i))
  unfold highLocalScore highLocalScoreNumerator highDensityResponseAction
  rw [sub_div, Finset.sum_div]
  have hfirst (e : E) :
      weights e * (∏ i, pReset e i) *
        responseMatrixAction q C (A e) c (fun c => highResponseProduct a V η g w φ c y) /
          ((∏ i, p i) * highResponseProduct a V η g w φ c y) =
      (weights e * (∏ i, pReset e i) / (∏ i, p i)) *
        responseMatrixAction q C (A e) c (fun v =>
          highResponseProduct a V η g w φ v y / highResponseProduct a V η g w φ c y) := by
    simp_rw [div_eq_mul_inv, mul_comm (highResponseProduct a V η g w φ _ y)
      (highResponseProduct a V η g w φ c y)⁻¹]
    rw [responseMatrixAction_mul]
    ring
  simp_rw [hfirst]
  congr 1
  have hp0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  calc
    _ = η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
        highResponseProduct a V η g w φ c y) := by field_simp [hp0, hL]
    _ = _ := by
      simp_rw [Finset.sum_div, mul_div_assoc,
        high_response_variance_ratio a V η g w φ c y _ hp]

/-- The genuine signed packet score depends only on local responses.
The density-reset weights are arbitrary actual fixed design quantities. -/
theorem high_local_score_depends_on_support {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highLocalScore q C a V η weights A p pReset g w φ c y =
      highLocalScore q C a V η weights A p pReset g w φ c y' := by
  rw [high_local_score_ratio_representation q C a V η weights A p pReset g w φ c y
      hpd (fun i => hp i (y i)),
    high_local_score_ratio_representation q C a V η weights A p pReset g w φ c y'
      hpd (fun i => hp i (y' i))]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    congr 1
    apply congrArg (responseMatrixAction q C (A e) c)
    funext v
    exact high_response_ratio_depends_on_support a V η g w φ c v S hw y y' hyy hp
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · rw [hyy i hi]
    · simp [hw i hi]

theorem high_local_score_measure_centered {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (ha : a ≠ 0) (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    (∫ y, highLocalScore q C a V η weights A p pReset g w φ c y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V
        ha (fun b => (hp i b).le))) = 0 := by
  rw [ternary_index_product_integral]
  exact high_local_score_centered q C a V η ha weights A p pReset g w φ c hpd
    (fun y => ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i))))

end FinitePacket

/-- Product-law orthogonality from local response dependence and actual
conditional centering. This helper is used below only with properties proved
from the explicit signed density-response packet. -/
theorem local_response_scores_orthogonal {n : ℕ}
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure (μ i)]
    (r s : (Fin n → Fin 3) → ℝ) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hr : ∀ y y', (∀ i ∈ S, y i = y' i) → r y = r y')
    (hs : ∀ y y', (∀ i ∈ T, y i = y' i) → s y = s y')
    (hc : (∫ y, r y ∂Measure.pi μ) = 0) :
    (∫ y, r y * s y ∂Measure.pi μ) = 0 := by
  let R (y : S → Fin 3) := r (extendPatchResponses n S y)
  let Q (y : T → Fin 3) := s (extendPatchResponses n T y)
  have hR (y : Fin n → Fin 3) : r y = R (fun i : S => y i) := by
    apply hr
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ (y : Fin n → Fin 3) : s y = Q (fun i : T => y i) := by
    apply hs
    intro i hi
    simp [extendPatchResponses, hi]
  have hcenter : (∫ y, R (fun i : S => y i) ∂Measure.pi μ) = 0 := by
    simpa only [← hR] using hc
  simp_rw [hR, hQ]
  exact finite_product_local_scores_orthogonal n μ S T hST R Q hcenter

section IntegratedPacket
variable {ι E Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [MeasurableSpace Z]

/-- The genuine separated packet action, before normalizing the response
likelihood. The positive outer mark measure is not presumed to have mass one. -/
def highIntegratedResponseAction {n : ℕ} (σ : Measure Z) (q : ℕ) (C a V η : ℝ)
    (weights : Z → E → ℝ) (A : Z → E → ι → ι → ℝ)
    (pReset : Z → E → Fin n → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∫ ζ, highDensityResponseAction q C (weights ζ) (A ζ) c
    (fun e => ∏ i, pReset ζ e i) (fun v => highResponseProduct a V η g w φ v y) ∂σ

def highIntegratedLocalScore {n : ℕ} (σ : Measure Z) (q : ℕ) (C a V η : ℝ)
    (weights : Z → E → ℝ) (A : Z → E → ι → ι → ℝ)
    (p : Fin n → ℝ) (pReset : Z → E → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : Fin n → Fin 3) : ℝ :=
  (highIntegratedResponseAction σ q C a V η weights A pReset g w φ c y -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)

theorem high_integrated_local_score_depends_on_support {n : ℕ} (σ : Measure Z)
    (q : ℕ) (C a V η : ℝ) (weights : Z → E → ℝ) (A : Z → E → ι → ι → ℝ)
    (p : Fin n → ℝ) (pReset : Z → E → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highIntegratedLocalScore σ q C a V η weights A p pReset g w φ c y =
      highIntegratedLocalScore σ q C a V η weights A p pReset g w φ c y' := by
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
  let B : ℝ := ∏ i, p i
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have hLy : highResponseProduct a V η g w φ c y ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
  have hLy' : highResponseProduct a V η g w φ c y' ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y' i)))
  have hvar' :
      (η ^ 2 * B * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
          (B * highResponseProduct a V η g w φ c y) =
      (η ^ 2 * B * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y' i) /
          (B * highResponseProduct a V η g w φ c y') := by
    calc
      _ = η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
          highResponseProduct a V η g w φ c y) := by field_simp [hB, hLy]
      _ = η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y' i) /
          highResponseProduct a V η g w φ c y') := by rw [hvar]
      _ = _ := by field_simp [hB, hLy']
  have hf (ζ : Z) :
      highDensityResponseAction q C (weights ζ) (A ζ) c (fun e => ∏ i, pReset ζ e i)
          (fun v => highResponseProduct a V η g w φ v y) /
            (B * highResponseProduct a V η g w φ c y) =
      highDensityResponseAction q C (weights ζ) (A ζ) c (fun e => ∏ i, pReset ζ e i)
          (fun v => highResponseProduct a V η g w φ v y') /
            (B * highResponseProduct a V η g w φ c y') := by
    have h := high_local_score_depends_on_support q C a V η (weights ζ) (A ζ) p
      (pReset ζ) g w φ c S hw y y' hyy hpd hp
    unfold highLocalScore highLocalScoreNumerator at h
    simp only [sub_div] at h
    change _ - _ = _ - _ at h
    dsimp [B] at hvar' ⊢
    linarith only [h, hvar']
  unfold highIntegratedLocalScore highIntegratedResponseAction
  rw [sub_div, sub_div]
  change _ - _ = _ - _
  dsimp [B] at hvar'
  rw [hvar']
  congr 1
  rw [← integral_div, ← integral_div]
  exact integral_congr_ae (Filter.Eventually.of_forall hf)

theorem high_density_response_action_sum_zero {n : ℕ} (q : ℕ) (C a V η : ℝ)
    (ha : a ≠ 0) (weights : E → ℝ) (A : E → ι → ι → ℝ)
    (pReset : E → Fin n → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) :
    ∑ y : Fin n → Fin 3, highDensityResponseAction q C weights A c
      (fun e => ∏ i, pReset e i) (fun v => highResponseProduct a V η g w φ v y) = 0 := by
  unfold highDensityResponseAction
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum, ← responseMatrixAction_sum]
  simp only [high_response_product_normalized a V η ha g w φ,
    responseMatrixAction_zero_mass, mul_zero]

theorem high_integrated_response_action_sum_zero {n : ℕ} (σ : Measure Z)
    (q : ℕ) (C a V η : ℝ) (ha : a ≠ 0)
    (weights : Z → E → ℝ) (A : Z → E → ι → ι → ℝ)
    (pReset : Z → E → Fin n → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hInt : ∀ y, Integrable (fun ζ => highDensityResponseAction q C (weights ζ) (A ζ) c
      (fun e => ∏ i, pReset ζ e i) (fun v => highResponseProduct a V η g w φ v y)) σ) :
    ∑ y : Fin n → Fin 3,
      highIntegratedResponseAction σ q C a V η weights A pReset g w φ c y = 0 := by
  unfold highIntegratedResponseAction
  rw [← integral_finsetSum Finset.univ (fun y _ => hInt y)]
  simp only [high_density_response_action_sum_zero q C a V η ha, integral_zero]

theorem high_integrated_local_score_centered {n : ℕ} (σ : Measure Z)
    (q : ℕ) (C a V η : ℝ) (ha : a ≠ 0)
    (weights : Z → E → ℝ) (A : Z → E → ι → ι → ℝ)
    (p : Fin n → ℝ) (pReset : Z → E → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hInt : ∀ y, Integrable (fun ζ => highDensityResponseAction q C (weights ζ) (A ζ) c
      (fun e => ∏ i, pReset ζ e i) (fun v => highResponseProduct a V η g w φ v y)) σ) :
    ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y *
      highIntegratedLocalScore σ q C a V η weights A p pReset g w φ c y = 0 := by
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have he (y : Fin n → Fin 3) :
      highResponseProduct a V η g w φ c y *
        highIntegratedLocalScore σ q C a V η weights A p pReset g w φ c y =
      (highIntegratedResponseAction σ q C a V η weights A pReset g w φ c y -
        η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 *
          highResponseVarianceTerm a V η g w φ c y i) / (∏ i, p i) := by
    have hL : highResponseProduct a V η g w φ c y ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
    unfold highIntegratedLocalScore
    field_simp [hB, hL]
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    high_integrated_response_action_sum_zero σ q C a V η ha weights A pReset g w φ c hInt,
    ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, high_response_variance_term_sum_zero,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_div]

theorem high_integrated_local_score_measure_centered {n : ℕ} (σ : Measure Z)
    (q : ℕ) (C a V η : ℝ) (ha : a ≠ 0)
    (weights : Z → E → ℝ) (A : Z → E → ι → ι → ℝ)
    (p : Fin n → ℝ) (pReset : Z → E → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hInt : ∀ y, Integrable (fun ζ => highDensityResponseAction q C (weights ζ) (A ζ) c
      (fun e => ∏ i, pReset ζ e i) (fun v => highResponseProduct a V η g w φ v y)) σ) :
    (∫ y, highIntegratedLocalScore σ q C a V η weights A p pReset g w φ c y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V
        ha (fun b => (hp i b).le))) = 0 := by
  rw [ternary_index_product_integral]
  exact high_integrated_local_score_centered σ q C a V η ha weights A p pReset
    g w φ c hpd hp hInt

/-- Integrability of the actual first packet action follows from integrable
weighted matrix entries and bounded measurable density resets. No score
moment, centering, or covariance conclusion is assumed. -/
theorem high_density_response_action_integrable {n : ℕ} (σ : Measure Z)
    (q : ℕ) (C : ℝ) (weights : Z → E → ℝ) (A : Z → E → ι → ι → ℝ)
    (pReset : Z → E → Fin n → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ)
    (hA : ∀ e i j, Integrable (fun ζ => weights ζ e * A ζ e i j) σ)
    (hReset : ∀ e i, Measurable (fun ζ => pReset ζ e i)) (pPlus : ℝ)
    (hpPlus : 0 ≤ pPlus) (hBound : ∀ ζ e i, |pReset ζ e i| ≤ pPlus) :
    Integrable (fun ζ => highDensityResponseAction q C (weights ζ) (A ζ) c
      (fun e => ∏ i, pReset ζ e i) Φ) σ := by
  have he (ζ : Z) (e : E) : weights ζ e * (∏ i, pReset ζ e i) *
      responseMatrixAction q C (A ζ e) c Φ =
      (∏ i, pReset ζ e i) *
        responseMatrixAction q C (fun i j => weights ζ e * A ζ e i j) c Φ := by
    rw [responseMatrixAction_scalar_matrix]
    ring
  simp only [highDensityResponseAction, he]
  apply integrable_finsetSum Finset.univ
  intro e _
  exact (responseMatrixAction_integrable σ q C _ (hA e) c Φ).bdd_mul
    (Finset.measurable_fun_prod _ (fun i _ => hReset e i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ζ => by
      simpa only [Real.norm_eq_abs] using
        finite_density_product_abs_bound (pReset ζ e) pPlus hpPlus (hBound ζ e)))

theorem high_separated_density_response_action_integrable {n : ℕ} (σ : Measure Z)
    (q : ℕ) (C : ℝ) (weights : E → ℝ) (A : Z → ι → ι → ℝ)
    (pReset : Z → E → Fin n → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hReset : ∀ e i, Measurable (fun ζ => pReset ζ e i)) (pPlus : ℝ)
    (hpPlus : 0 ≤ pPlus) (hBound : ∀ ζ e i, |pReset ζ e i| ≤ pPlus) :
    Integrable (fun ζ => highDensityResponseAction q C weights (fun _ => A ζ) c
      (fun e => ∏ i, pReset ζ e i) Φ) σ := by
  exact high_density_response_action_integrable σ q C (fun _ => weights)
    (fun ζ _ => A ζ) pReset c Φ
    (fun e i j => (separatedMatrix_entry_integrable σ A hA hcost i j).const_mul (weights e))
    hReset pPlus hpPlus hBound

end IntegratedPacket

section Family
variable {J ι E Z : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
  [Fintype E] [MeasurableSpace Z]

/-- Actual separated density-response scores on disjoint coordinate patches
are orthogonal under the true conditional response law. Every centering and
locality fact is discharged from the packet definitions. -/
theorem high_integrated_packet_scores_orthogonal {n : ℕ}
    (σ : J → Measure Z) (q : J → ℕ) (C a V η : ℝ) (ha : a ≠ 0)
    (weights : J → Z → E → ℝ) (A : J → Z → E → ι → ι → ℝ)
    (p : Fin n → ℝ) (pReset : J → Z → E → Fin n → ℝ)
    (g w : J → Fin n → ℝ) (φ : J → Fin n → ι → ℝ) (c : J → ι → ℝ)
    (f : Fin n → ℝ) (hreg : ∀ j, coefficientRegression η (g j) (w j) (φ j) (c j) = f)
    (S : J → Finset (Fin n)) (hw : ∀ j i, i ∉ S j → w j i = 0)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hInt : ∀ j y, Integrable (fun ζ =>
      highDensityResponseAction (q j) C (weights j ζ) (A j ζ) (c j)
        (fun e => ∏ i, pReset j ζ e i)
        (fun v => highResponseProduct a V η (g j) (w j) (φ j) v y)) (σ j))
    (j l : J) (hST : Disjoint (S j) (S l)) :
    (∫ y, highIntegratedLocalScore (σ j) (q j) C a V η (weights j) (A j) p
      (pReset j) (g j) (w j) (φ j) (c j) y *
      highIntegratedLocalScore (σ l) (q l) C a V η (weights l) (A l) p
        (pReset l) (g l) (w l) (φ l) (c l) y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le))) = 0 := by
  let μ : Fin n → Measure (Fin 3) := fun i =>
    ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le)
  have hp' (j : J) (i : Fin n) (b : Fin 3) :
      0 < ternaryMass a (coefficientRegression η (g j) (w j) (φ j) (c j) i) V b := by
    rw [hreg j]
    exact hp i b
  apply local_response_scores_orthogonal μ _ _ (S j) (S l) hST
  · intro y y' hyy
    exact high_integrated_local_score_depends_on_support (σ j) (q j) C a V η
      (weights j) (A j) p (pReset j) (g j) (w j) (φ j) (c j) (S j) (hw j)
      y y' hyy hpd (hp' j)
  · intro y y' hyy
    exact high_integrated_local_score_depends_on_support (σ l) (q l) C a V η
      (weights l) (A l) p (pReset l) (g l) (w l) (φ l) (c l) (S l) (hw l)
      y y' hyy hpd (hp' l)
  · have h := high_integrated_local_score_measure_centered (σ j) (q j) C a V η ha
      (weights j) (A j) p (pReset j) (g j) (w j) (φ j) (c j) hpd (hp' j) (hInt j)
    simpa only [hreg j] using h

end Family

/-- The actual observation indices in a torus patch. -/
def highPatchSampleIndices (d k n : ℕ) (j : HighWindowLabels d k)
    (x : Fin n → Covariate d) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ∈ highTorusPatch d k j)

theorem highPatchSampleIndices_disjoint (d k n : ℕ) [NeZero k]
    (x : Fin n → Covariate d) (j l : HighWindowLabels d k)
    (hjl : l ∉ highNeighborLabels d k j) :
    Disjoint (highPatchSampleIndices d k n j x) (highPatchSampleIndices d k n l x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp (highTorusPatch_disjoint_of_not_neighbor d k j l hjl)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem highPeriodicTensor_sample_zero_outside_patch (d k n : ℕ)
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) (i : Fin n)
    (hi : i ∉ highPatchSampleIndices d k n j x) :
    highPeriodicTensor d k j (x i) = 0 := by
  by_contra h
  have hx := highPeriodicTensor_supported_patch d k j h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩)

end NearlyMinimax
