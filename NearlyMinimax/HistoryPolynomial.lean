module

public import Mathlib


@[expose] public section

/-!
# The actual finite heap deletion polynomial

For a finite partially ordered history, coefficients enumerate all successive
deletions of maximal pieces, with their signed mark weights. Dividing the
degree-k coefficient by k! is the combinatorial order-volume coefficient.
The derivative identity is proved from this enumeration, without assuming
a transport recurrence.
-/

noncomputable section
namespace NearlyMinimax

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def historyMaximalPieces (S : Finset α) : Finset α := by
  classical
  exact S.filter (fun x => ∀ y ∈ S, x ≤ y → y = x)

theorem mem_historyMaximalPieces {S : Finset α} {x : α} :
    x ∈ historyMaximalPieces S ↔ x ∈ S ∧ ∀ y ∈ S, x ≤ y → y = x := by
  classical
  simp only [historyMaximalPieces, Finset.mem_filter]

theorem historyMaximalPieces_subset (S : Finset α) : historyMaximalPieces S ⊆ S := by
  intro x hx
  exact (mem_historyMaximalPieces.1 hx).1

def historyDeletionCoefficient (weight : α → ℝ) : ℕ → Finset α → ℝ
  | 0, _ => 1
  | k + 1, S => ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x)

@[simp] theorem historyDeletionCoefficient_zero (weight : α → ℝ) (S : Finset α) :
    historyDeletionCoefficient weight 0 S = 1 := rfl

@[simp] theorem historyDeletionCoefficient_succ (weight : α → ℝ) (k : ℕ) (S : Finset α) :
    historyDeletionCoefficient weight (k + 1) S =
      ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x) := rfl

theorem historyDeletionCoefficient_above_card (weight : α → ℝ) (k : ℕ) (S : Finset α)
    (hk : S.card < k) : historyDeletionCoefficient weight k S = 0 := by
  induction k generalizing S with
  | zero => omega
  | succ k ih =>
    rw [historyDeletionCoefficient_succ]
    apply Finset.sum_eq_zero
    intro x hx
    have hxS := historyMaximalPieces_subset S hx
    have hcard := Finset.card_erase_of_mem hxS
    have hpos := Finset.card_pos.2 ⟨x, hxS⟩
    rw [ih (S.erase x) (by omega), mul_zero]

def historyDeletionPolynomial (weight : α → ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (S.card + 1), t ^ k / (k.factorial : ℝ) * historyDeletionCoefficient weight k S

@[simp] theorem historyDeletionPolynomial_at_zero (weight : α → ℝ) (S : Finset α) :
    historyDeletionPolynomial weight S 0 = 1 := by
  unfold historyDeletionPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

theorem historyDeletionPolynomial_derivative_formula (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyDeletionPolynomial weight S)
      (∑ k ∈ Finset.range (S.card + 1),
        (k : ℝ) * t ^ (k - 1) / (k.factorial : ℝ) * historyDeletionCoefficient weight k S) t := by
  apply HasDerivAt.fun_sum
  intro k hk
  simpa only [id_eq, mul_one] using! (((hasDerivAt_id t).pow k).div_const (k.factorial : ℝ)).mul_const
    (historyDeletionCoefficient weight k S)

theorem historyDeletionPolynomial_derivative_shift (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    (∑ k ∈ Finset.range (S.card + 1),
      (k : ℝ) * t ^ (k - 1) / (k.factorial : ℝ) * historyDeletionCoefficient weight k S) =
    ∑ k ∈ Finset.range S.card, t ^ k / (k.factorial : ℝ) * historyDeletionCoefficient weight (k + 1) S := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorial_succ]
  push_cast
  field_simp

theorem historyDeletionPolynomial_derivative_deletion (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    (∑ k ∈ Finset.range S.card, t ^ k / (k.factorial : ℝ) * historyDeletionCoefficient weight (k + 1) S) =
      ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) t := by
  simp_rw [historyDeletionCoefficient_succ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hxS := historyMaximalPieces_subset S hx
  have hc : (S.erase x).card + 1 = S.card := by
    have hcard := Finset.card_erase_of_mem hxS
    have hpos := Finset.card_pos.2 ⟨x, hxS⟩
    omega
  unfold historyDeletionPolynomial
  rw [hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The genuine finite deletion polynomial satisfies the exact source derivative identity. -/
theorem historyDeletionPolynomial_hasDerivAt (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyDeletionPolynomial weight S)
      (∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) t) t := by
  have hh := historyDeletionPolynomial_derivative_formula weight S t
  rw [historyDeletionPolynomial_derivative_shift, historyDeletionPolynomial_derivative_deletion] at hh
  exact hh

end NearlyMinimax
