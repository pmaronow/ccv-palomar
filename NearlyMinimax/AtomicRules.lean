module

public import NearlyMinimax.DerivativeRule
public import Mathlib.MeasureTheory.VectorMeasure.Integral


@[expose] public section

/-! Actual finite signed measures representing the paper's finite moment rules. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators ENNReal
open MeasureTheory VectorMeasure Polynomial

section Atomic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- A finite atomic signed measure, retaining all weights even if atoms coincide. -/
def atomicSignedRule (z : ι → X) (w : ι → ℝ) : SignedMeasure X :=
  ∑ i, VectorMeasure.dirac (z i) (w i)

/-- The positive measure of absolute atom weights dominates the total variation. -/
def atomicVariationBound (z : ι → X) (w : ι → ℝ) : Measure X :=
  ∑ i, ‖w i‖₊ • Measure.dirac (z i)

private theorem atomic_dirac_integrable (x : X) (w : ℝ) (f : X → ℝ) :
    (VectorMeasure.dirac x w).Integrable f := by
  change Integrable f (VectorMeasure.dirac x w).variation
  rw [VectorMeasure.variation_dirac]
  change Integrable f (‖w‖₊ • Measure.dirac x)
  exact (integrable_dirac (by exact enorm_lt_top)).smul_measure_nnreal

theorem atomicSignedRule_integrable (z : ι → X) (w : ι → ℝ) (f : X → ℝ) :
    (atomicSignedRule z w).Integrable f := by
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro i hi
  exact atomic_dirac_integrable _ _ _

/-- Integration against the actual signed measure equals the original finite-sum action. -/
theorem atomicSignedRule_integral (z : ι → X) (w : ι → ℝ) (f : X → ℝ) :
    ∫ᵛ x, f x ∂<•(atomicSignedRule z w) = ∑ i, w i * f (z i) := by
  rw [atomicSignedRule, integral_finsetSum_vectorMeasure
    (fun i hi => atomic_dirac_integrable (z i) (w i) f)]
  simp [mul_comm]

theorem atomicSignedRule_variation_le (z : ι → X) (w : ι → ℝ) :
    (atomicSignedRule z w).variation ≤ atomicVariationBound z w := by
  apply (VectorMeasure.variation_finsetSum_le Finset.univ _).trans_eq
  simp only [VectorMeasure.variation_dirac]
  rfl

instance atomicVariationBound_finite (z : ι → X) (w : ι → ℝ) :
    IsFiniteMeasure (atomicVariationBound z w) := by
  unfold atomicVariationBound
  infer_instance

instance atomicSignedRule_variation_finite (z : ι → X) (w : ι → ℝ) :
    IsFiniteMeasure (atomicSignedRule z w).variation :=
  isFiniteMeasure_of_le (atomicVariationBound z w) (atomicSignedRule_variation_le z w)

end Atomic

/-- The exterior interpolation rule as an actual real signed measure. -/
def exteriorSignedRule (a b : ℝ) (n : ℕ) : SignedMeasure ℝ :=
  atomicSignedRule (exteriorNode a b n) (exteriorWeight a b n)

theorem exteriorSignedRule_exact (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 1 ≤ n)
    (P : ℝ[X]) (hP : P.degree ≤ n) :
    ∫ᵛ z, P.eval z ∂<•(exteriorSignedRule a b n) = P.eval 0 := by
  rw [exteriorSignedRule, atomicSignedRule_integral]
  exact exterior_rule_exact a b hab n hn P hP

/-- The differentiated Chebyshev rule as an actual real signed measure. -/
def derivativeSignedRule (D : ℕ) : SignedMeasure ℝ :=
  atomicSignedRule (lobattoNode (2 * ((D - 1) / 2) + 1)) (lobattoDerivativeWeight ((D - 1) / 2))

theorem derivativeSignedRule_exact (D : ℕ) (hD : 1 ≤ D) (P : ℝ[X]) (hP : P.degree ≤ D) :
    ∫ᵛ z, P.eval z ∂<•(derivativeSignedRule D) = P.derivative.eval 0 := by
  rw [derivativeSignedRule, atomicSignedRule_integral]
  exact derivative_rule_exact D hD P hP

/-- The response-coefficient extraction rule as an actual real signed measure. -/
def responseSignedRule (q : ℕ) : SignedMeasure ℝ := atomicSignedRule (responseNode q) (responseWeight q)

theorem responseSignedRule_moments (q a : ℕ) (ha : a ≤ 2 * q + 1) :
    ∫ᵛ z, z ^ a ∂<•(responseSignedRule q) = if a = 2 then 1 else 0 := by
  rw [responseSignedRule, atomicSignedRule_integral]
  exact response_rule_moments q a ha

end NearlyMinimax
