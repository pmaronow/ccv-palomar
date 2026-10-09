module

public import NearlyMinimax.HighUnionScore
public import NearlyMinimax.HighSelectedScoreEnergy


@[expose] public section

/-! Exact reduction of the complete marked score to observations inside
its true patch. Density resets and regression windows are unchanged
outside the selected coordinates, so their likelihood factors cancel. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem finite_product_split_embedding {n r : ℕ} (e : Fin r ↪ Fin n) (F : Fin n → ℝ) :
    (∏ i : Fin n, F i) =
      (∏ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e, F i) * ∏ l : Fin r, F (e l) := by
  rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.map e))]
  rw [Finset.prod_map]

theorem finite_sum_split_embedding {n r : ℕ} (e : Fin r ↪ Fin n) (F : Fin n → ℝ) :
    (∑ i : Fin n, F i) =
      (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e, F i) + ∑ l : Fin r, F (e l) := by
  rw [← Finset.sum_sdiff (Finset.subset_univ (Finset.univ.map e))]
  rw [Finset.sum_map]

section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

theorem high_marked_local_score_ratio {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      (∫ z, activation z * (∏ i, pReset z i / p i) *
        ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i) ∂π) -
      η ^ 2 * ∑ i, (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i)) := by
  have hpP : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have hqP : highResponseProduct a V η g w φ c y ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
  unfold highMarkedLocalScore highMarkedResponseAction
  rw [sub_div, ← integral_div]
  have hfirst : (fun z => activation z * (∏ i, pReset z i) *
      highResponseProduct a V η g w φ (cReset z) y /
        ((∏ i, p i) * highResponseProduct a V η g w φ c y)) =
      (fun z => activation z * (∏ i, pReset z i / p i) *
        ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i)) := by
    funext z
    simp only [Finset.prod_div_distrib]
    unfold highResponseProduct
    field_simp [hpP, hqP]
  rw [hfirst]
  congr 1
  calc
    _ = η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
        highResponseProduct a V η g w φ c y) := by field_simp [hpP, hqP]
    _ = _ := by
      simp_rw [Finset.sum_div, mul_div_assoc,
        high_response_variance_ratio a V η g w φ c y _ (fun i => hp i (y i))]

theorem high_marked_local_score_selected {n r : ℕ} (e : Fin r ↪ Fin n)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
        cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) := by
  rw [high_marked_local_score_ratio π activation a V η p pReset cReset g w φ c y hpd hp,
    high_marked_local_score_ratio π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) (fun l => hpd (e l))
      (fun l b => hp (e l) b)]
  have hprod (z : E) :
      (∏ i, pReset z i / p i) *
          ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
            ternaryMass a (coefficientRegression η g w φ c i) V (y i) =
      (∏ l : Fin r, pReset z (e l) / p (e l)) *
          ∏ l : Fin r, ternaryMass a (coefficientRegression η g w φ (cReset z) (e l)) V (y (e l)) /
            ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      finite_product_split_embedding e]
    have ho : (∏ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e,
        (pReset z i / p i) *
          (ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
            ternaryMass a (coefficientRegression η g w φ c i) V (y i))) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hiS := (Finset.mem_sdiff.mp hi).2
      rw [hReset z i hiS, div_self (hpd i)]
      have hv : coefficientRegression η g w φ (cReset z) i = coefficientRegression η g w φ c i := by
        simp [coefficientRegression, hw i hiS]
      rw [hv, div_self (hp i (y i)).ne', one_mul]
    rw [ho, one_mul]
  have hsum : (∑ i, (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
      ternaryMass a (coefficientRegression η g w φ c i) V (y i))) =
      ∑ l : Fin r, (w (e l)) ^ 2 * (ternaryVarianceDerivative a (y (e l)) /
        ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l))) := by
    rw [finite_sum_split_embedding e]
    have ho : (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e,
        (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hw i (Finset.mem_sdiff.mp hi).2]
    rw [ho, zero_add]
  simp_rw [mul_assoc, hprod, hsum]
  rfl

end
end NearlyMinimax
