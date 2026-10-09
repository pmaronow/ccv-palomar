module

public import NearlyMinimax.HighSelectedScoreEnergy


@[expose] public section

/-! Exact response-configuration sums and their normalized-design transfer.
The factor `3^n` is the cardinality of the genuine ternary response space. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem finite_configuration_integrable_bound {I X : Type*} [Fintype I]
    [MeasurableSpace X] (μ : Measure X) (f : I → X → ℝ) (K : ℝ)
    (hi : ∀ i, Integrable (f i) μ) (hK : ∀ i, (∫ x, f i x ∂μ) ≤ K) :
    Integrable (fun x => ∑ i, f i x) μ ∧
      (∫ x, ∑ i, f i x ∂μ) ≤ (Fintype.card I : ℝ) * K := by
  classical
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hK i)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem ternary_configuration_square_integrable_bound {X : Type*}
    [MeasurableSpace X] (μ : Measure X) (n : ℕ)
    (R : X → (Fin n → Fin 3) → ℝ) (K : ℝ)
    (hi : ∀ y, Integrable (fun x => R x y ^ 2) μ)
    (hK : ∀ y, (∫ x, R x y ^ 2 ∂μ) ≤ K) :
    Integrable (fun x => ∑ y : Fin n → Fin 3, R x y ^ 2) μ ∧
      (∫ x, ∑ y : Fin n → Fin 3, R x y ^ 2 ∂μ) ≤ (3 : ℝ) ^ n * K := by
  have h := finite_configuration_integrable_bound μ (fun y x => R x y ^ 2) K hi hK
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

theorem selected_raw_square_integrable_bound {κ α : Type*} [Fintype κ] [MeasurableSpace α]
    (μ : Measure (κ → α)) (R : (κ → α) → (κ → Fin 3) → ℝ) (K : ℝ)
    (hi : ∀ y, Integrable (fun x => R x y ^ 2) μ)
    (hK : ∀ y, (∫ x, R x y ^ 2 ∂μ) ≤ K) :
    Integrable (selectedRawSquareEnergy R) μ ∧
      (∫ x, selectedRawSquareEnergy R x ∂μ) ≤ (3 : ℝ) ^ Fintype.card κ * K :=
  by
    unfold selectedRawSquareEnergy
    have h := finite_configuration_integrable_bound μ (fun y x => R x y ^ 2) K hi hK
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

theorem normalized_selected_response_configuration_bound {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set α) (hA : MeasurableSet A) (m pMinus cMass K : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (p : α → ℝ) (hpMeas : Measurable p) (q : α → Fin 3 → ℝ)
    (hqMeas : ∀ y, Measurable (fun x => q x y))
    (R : (Fin n → α) → (Fin n → Fin 3) → ℝ)
    (hR : ∀ y, Measurable (fun x => R x y))
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ A, pMinus ≤ p x) (hq : ∀ x ∈ A, ∀ y, cMass ≤ q x y)
    (hi : ∀ y, Integrable (fun x => R x y ^ 2) (Measure.pi (fun _ : Fin n => μ.restrict A)))
    (hK : ∀ y, (∫ x, R x y ^ 2 ∂Measure.pi (fun _ : Fin n => μ.restrict A)) ≤ K) :
    Integrable (selectedConditionalScoreEnergy p q R)
      (Measure.pi (fun _ : Fin n => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ∧
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ : Fin n => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ≤
        (3 * highFixedScoreDenominator pMinus cMass) ^ n * K := by
  have hraw := selected_raw_square_integrable_bound
    (Measure.pi (fun _ : Fin n => μ.restrict A)) R K hi hK
  have hs := normalized_selected_score_energy_integrable_bound μ A hA m pMinus cMass
    hpMinus hcMass hm p hpMeas q hqMeas R hR hprob hp hq hraw.1
  refine ⟨hs.1, hs.2.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hraw.2
    (pow_nonneg (high_fixed_score_denominator_pos hpMinus hcMass).le n)
  simpa only [Fintype.card_fin, mul_pow, mul_assoc, mul_comm, mul_left_comm] using h

end NearlyMinimax
