module

public import NearlyMinimax.HighUnionScore


@[expose] public section

/-! Exact sum of window scores under a genuine squared partition of unity.
This algebra counts the common variance derivative once. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

 theorem highMarkedLocalScore_sum_of_partition {J ι E : Type*}
    [Fintype J] [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {n : ℕ}
    (π : J → Measure E) (activation : J → E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : J → E → Fin n → ℝ)
    (cReset : J → E → ι → ℝ) (g w : J → Fin n → ℝ)
    (φ : J → Fin n → ι → ℝ) (c : J → ι → ℝ) (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j) (w j) (φ j) (c j) = f)
    (hpartition : ∀ i, ∑ j, (w j i)^2 = 1) (y : Fin n → Fin 3) :
    (∑ j, highMarkedLocalScore (π j) (activation j) a V η p (pReset j)
      (cReset j) (g j) (w j) (φ j) (c j) y) =
    ((∑ j, highMarkedResponseAction (π j) (activation j) a V η
      (pReset j) (cReset j) (g j) (w j) (φ j) y) -
      η^2*(∏ i, p i)*∑ i, ternaryVarianceDerivative a (y i)*
        ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (f l) V (y l)) /
      ((∏ i, p i)*∏ i, ternaryMass a (f i) V (y i)) := by
  unfold highMarkedLocalScore highResponseProduct highResponseVarianceTerm
  simp_rw [hreg]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  congr 2
  calc
    (∑ j, η^2*(∏ i, p i)*∑ i, (w j i)^2 *
        (ternaryVarianceDerivative a (y i)*∏ l ∈ Finset.univ.erase i,
          ternaryMass a (f l) V (y l))) =
      η^2*(∏ i, p i)*∑ j, ∑ i, (w j i)^2 *
        (ternaryVarianceDerivative a (y i)*∏ l ∈ Finset.univ.erase i,
          ternaryMass a (f l) V (y l)) := by rw [Finset.mul_sum]
    _ = η^2*(∏ i, p i)*∑ i, ∑ j, (w j i)^2 *
        (ternaryVarianceDerivative a (y i)*∏ l ∈ Finset.univ.erase i,
          ternaryMass a (f l) V (y l)) := by rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, hpartition, one_mul]

end NearlyMinimax
