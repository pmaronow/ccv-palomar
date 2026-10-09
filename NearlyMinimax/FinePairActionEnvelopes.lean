module

public import NearlyMinimax.FinePairResponseBounds
public import NearlyMinimax.HighFrameLocalBounds


@[expose] public section

/-! Bounds on the actual pair alias and even-field remainder. The response
cap follows from the genuine finite response packet and chart frame. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem fine_pair_filtered_sum_abs_bound {I : Type*} (s : Finset I) (P : I → Prop) [DecidablePred P]
    (c H : I → ℝ) (R B K : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ s, |c i| ≤ B) (hR : |R| ≤ K) :
    |∑ i ∈ s, c i * (if P i then 1 else 0) * H i * R| ≤
      B*K * ∑ i ∈ s, if P i then |H i| else 0 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hP : P i
  · simp only [if_pos hP, mul_one]
    calc
      _ = (|c i| * |R|) * |H i| := by rw [abs_mul, abs_mul]; ring
      _ ≤ (B*K) * |H i| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hc i hi) hR (abs_nonneg _) hB) (abs_nonneg _)
  · simp [hP]

section Actual
variable {d n F : ℕ}

theorem finePairDistance_response_bound_of_chart (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (g w : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    |responseMatrixAction q C (finePairDistanceMatrix d F) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
        finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2 :=
  finePairDistance_response_all_count_bound q hn C a V η ρ (lt_of_lt_of_le zero_lt_one hC)
    ha hη hρ hηρ U g w c y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp

theorem finePairPairAliasAction_abs_bound_of_chart
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    |finePairPairAliasAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
      finePairDensityCoefficientBudget ad bd M n *
        (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2) *
          ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
            if W.card = 2 then |finePairTimeSubsetMoment T0 N U W| else 0 := by
  unfold finePairPairAliasAction
  exact fine_pair_filtered_sum_abs_bound ((Finset.univ : Finset (Fin n)).powerset) (fun W => W.card = 2)
    (fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i)
    (fun W => finePairTimeSubsetMoment T0 N U W) _ _ _
    (finePairDensityCoefficientBudget_nonneg ad bd (haD.trans hab).le M n)
    (fun W _ => finePairCountCoefficient_product_bound ad bd haD hab M p hpD W)
    (finePairDistance_response_bound_of_chart q hn C a V η ρ hC ha hη hρ hηρ U hU g w c y hc hg hw hp)

theorem finePairEvenFieldAction_abs_bound_of_chart
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    |finePairEvenFieldAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
      finePairDensityCoefficientBudget ad bd M n *
        (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2) *
          ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
            if 4 ≤ W.card ∧ Even W.card then |finePairTimeSubsetMoment T0 N U W| else 0 := by
  unfold finePairEvenFieldAction
  exact fine_pair_filtered_sum_abs_bound ((Finset.univ : Finset (Fin n)).powerset) (fun W => 4 ≤ W.card ∧ Even W.card)
    (fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i)
    (fun W => finePairTimeSubsetMoment T0 N U W) _ _ _
    (finePairDensityCoefficientBudget_nonneg ad bd (haD.trans hab).le M n)
    (fun W _ => finePairCountCoefficient_product_bound ad bd haD hab M p hpD W)
    (finePairDistance_response_bound_of_chart q hn C a V η ρ hC ha hη hρ hηρ U hU g w c y hc hg hw hp)

end Actual
end NearlyMinimax
