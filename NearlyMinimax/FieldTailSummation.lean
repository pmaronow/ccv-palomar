module

public import NearlyMinimax.DefectTailSummation


@[expose] public section

/-! True finite factorial summation of the higher-field term, whose first
possible selected count is four. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

def fieldTailConstant (Csharp C : ℝ) : ℝ :=
  Real.exp (Csharp * C) * poissonCountWeight (Csharp * C) 4

theorem finite_geometric_field_count_tail_le {P Csharp C mu : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (4 + j) ≤ P * C ^ (4 + j)) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (4 + j) * R (4 + j)) ≤
      fieldTailConstant Csharp C * P * mu ^ 4 := by
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (4 + j) * R (4 + j) ≤
      P * mu ^ 4 * poissonCountWeight (Csharp * C) (4 + j) := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (4 + j))
    apply h.trans
    have hp : mu ^ (4 + j) ≤ mu ^ 4 := by
      rw [pow_add]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hmu hmu1) (pow_nonneg hmu 4)).trans_eq (mul_one _)
    have hh := mul_le_mul_of_nonneg_left hp
      (mul_nonneg hP (poissonCountWeight_nonneg (mul_nonneg hCs hC) (4 + j)))
    convert hh using 1 <;> unfold poissonCountWeight <;> simp only [mul_pow] <;> ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left
    (finite_poissonCountWeight_tail_le (mul_nonneg hCs hC) 4 J)
    (mul_nonneg hP (pow_nonneg hmu 4))
  apply (hs.trans ht).trans_eq
  unfold fieldTailConstant
  ring

theorem finite_polynomial_field_count_tail_le {P Csharp C mu : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (a J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (4 + j) ≤ P * C ^ (4 + j) * (4 + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (4 + j) * R (4 + j)) ≤
      fieldTailConstant Csharp (C * 2 ^ a) * P * mu ^ 4 := by
  apply finite_geometric_field_count_tail_le hP hCs (by positivity) hmu hmu1 J R
  intro j hj
  apply (hR j hj).trans
  have h := mul_le_mul_of_nonneg_left (polynomial_count_factor_le (4 + j) a)
    (by positivity : 0 ≤ P * C ^ (4 + j))
  simpa only [mul_pow, ← mul_assoc] using h

end NearlyMinimax
