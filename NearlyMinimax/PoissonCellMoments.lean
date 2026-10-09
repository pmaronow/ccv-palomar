module

public import NearlyMinimax.PoissonCellField
public import NearlyMinimax.EvenCellPairs


@[expose] public section

/-! Exact occupancy moments of the constructed Poisson cell field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

theorem partitionFieldFiber_product_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (n j : ℕ)
    (U : Fin j → X) :
    Integrable (fun z : partitionFieldFiber H n => ∏ l, partitionFieldFiberValue ρ z (U l))
      (partitionFieldFiberLaw μ n) := by
  apply Integrable.of_bound
    (Finset.measurable_prod _ (fun l _ =>
      partitionFieldFiberValue_measurable_fixed ρ hρ n (U l))).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun z => by
    simp only [Real.norm_eq_abs, Finset.abs_prod, partitionFieldFiberValue_abs,
      Finset.prod_const_one, le_refl])

theorem partitionFieldFiber_product_moment (μ : Measure H) [IsProbabilityMeasure μ]
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (n j : ℕ)
    (U : Fin j → X) :
    (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) =
      ∫ h, if ∀ p : Fin n → Fin 2,
        Even ((Finset.univ.filter (fun l => partitionFieldPattern ρ h (U l) = p)).card)
        then (1 : ℝ) else 0 ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [partitionFieldFiberLaw, integral_prod _
    (partitionFieldFiber_product_integrable μ ρ hρ n j U)]
  simp only [partitionFieldFiberValue, cellSign_product_moment]

theorem partitionFieldFiber_odd_moment (μ : Measure H) [IsProbabilityMeasure μ]
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (n j : ℕ)
    (U : Fin j → X) (hj : Odd j) :
    (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) = 0 := by
  rw [partitionFieldFiberLaw, integral_prod _
    (partitionFieldFiber_product_integrable μ ρ hρ n j U)]
  simp only [partitionFieldFiberValue]
  have ho (h : Fin n → H) := cellSign_product_odd_moment
    (I := Fin n → Fin 2) (J := Fin j) (fun l => partitionFieldPattern ρ h (U l))
      (by simpa only [Fintype.card_fin] using hj)
  simp_rw [ho]
  simp

theorem poissonCellField_odd_moment (μ : Measure H) [IsProbabilityMeasure μ]
    (r : ℝ≥0) (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (j : ℕ)
    (U : Fin j → X) (hj : Odd j) :
    (∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r) = 0 := by
  rw [poissonCellField_integral_series μ r (fun z => ∏ l, poissonCellFieldValue ρ z (U l))
    (Finset.measurable_prod _ (fun l _ => poissonCellFieldValue_measurable_fixed ρ hρ (U l)))
    (fun z => by simp only [Finset.abs_prod, poissonCellFieldValue_abs,
      Finset.prod_const_one, le_refl])]
  simp only [poissonCellFieldValue, partitionFieldFiber_odd_moment μ ρ hρ _ j U hj,
    mul_zero, tsum_zero]

theorem poissonCellField_product_moment_nonneg (μ : Measure H) [IsProbabilityMeasure μ]
    (r : ℝ≥0) (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (j : ℕ)
    (U : Fin j → X) :
    0 ≤ ∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r := by
  rw [poissonCellField_integral_series μ r (fun z => ∏ l, poissonCellFieldValue ρ z (U l))
    (Finset.measurable_prod _ (fun l _ => poissonCellFieldValue_measurable_fixed ρ hρ (U l)))
    (fun z => by simp only [Finset.abs_prod, poissonCellFieldValue_abs,
      Finset.prod_const_one, le_refl])]
  apply tsum_nonneg
  intro n
  simp only [poissonCellFieldValue, partitionFieldFiber_product_moment μ ρ hρ]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro h
  dsimp only [Pi.zero_apply]
  split_ifs <;> norm_num

end NearlyMinimax
