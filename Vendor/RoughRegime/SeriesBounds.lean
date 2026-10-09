module

public import Mathlib


@[expose] public section

/-!
The combined-index coefficient and tail estimates used in Lemma 5(a).
These generic results are separated from the unproved determinant power-series bridge.
-/
noncomputable section
open scoped BigOperators
namespace RoughRegime.SeriesBounds

lemma weighted_geometric_summable (ν : ℕ) (ρ : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hp] using h1
  have hraw := summable_pow_mul_geometric_of_norm_lt_one ν hn
  have hshift : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr hraw
  convert hshift.mul_right ρ⁻¹ using 1
  ext k
  rw [pow_succ]
  field_simp

/-- The exact tail bound used in Lemma 5(a), valid in every complete normed space. -/
theorem series_truncation_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (ν m : ℕ) (ρ A : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) (hA : 0 ≤ A)
    (hcoeff : ∀ k : ℕ, ‖f k‖ ≤ A * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) :
    ‖(∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k‖ ≤
      A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by
  let w : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k
  have hw : Summable w := weighted_geometric_summable ν ρ hp h1
  have hmajor : Summable (fun k : ℕ => A * w k) := hw.mul_left A
  have hcoeff' (k : ℕ) : ‖f k‖ ≤ A * w k := by
    simpa only [w, mul_assoc] using hcoeff k
  have hnorm : Summable (fun k : ℕ => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeff' hmajor
  have hf : Summable f := hmajor.of_norm_bounded hcoeff'
  have htail : (∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k =
      ∑' k : ℕ, f (k + (m + 1)) := by
    have h := hf.sum_add_tsum_nat_add (m + 1)
    rw [← h]
    abel
  have hn0 : Summable (fun k : ℕ => ‖f (k + m)‖) :=
    (summable_nat_add_iff (f := fun k => ‖f k‖) m).mpr hnorm
  have hn1 : Summable (fun k : ℕ => ‖f (k + (m + 1))‖) :=
    (summable_nat_add_iff (f := fun k => ‖f k‖) (m + 1)).mpr hnorm
  have htmono : (∑' k : ℕ, ‖f (k + (m + 1))‖) ≤ ∑' k : ℕ, ‖f (k + m)‖ := by
    have h := hn0.tsum_eq_zero_add
    simp only [zero_add] at h
    have he : (fun k : ℕ => ‖f (k + 1 + m)‖) = (fun k : ℕ => ‖f (k + (m + 1))‖) := by
      ext k
      congr 2
      omega
    rw [he] at h
    rw [h]
    exact le_add_of_nonneg_left (norm_nonneg _)
  let C := A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htbound (k : ℕ) : ‖f (k + m)‖ ≤ C * w k := by
    apply (hcoeff (k + m)).trans
    have hindex : (k + m + 1 : ℝ) ≤ (m + 1) * (k + 1) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (k + m + 1 : ℝ)) hindex ν
    have hpow' : (((k + m + 1 : ℕ) : ℝ)) ^ ν ≤
        ((m + 1 : ℕ) : ℝ) ^ ν * ((k + 1 : ℕ) : ℝ) ^ ν := by
      simpa [mul_pow] using hpow
    have hmul := mul_le_mul_of_nonneg_left hpow' hA
    have hmul' := mul_le_mul_of_nonneg_right hmul (pow_nonneg hp.le (k + m))
    dsimp [C, w]
    convert hmul' using 1 <;> rw [pow_add] <;> ring
  have hsbound : (∑' k : ℕ, ‖f (k + m)‖) ≤ ∑' k : ℕ, C * w k :=
    Summable.tsum_le_tsum htbound hn0 (hw.mul_left C)
  rw [htail]
  calc
    _ ≤ ∑' k : ℕ, ‖f (k + (m + 1))‖ := norm_tsum_le_tsum_norm hn1
    _ ≤ ∑' k : ℕ, ‖f (k + m)‖ := htmono
    _ ≤ ∑' k : ℕ, C * w k := hsbound
    _ = _ := by rw [tsum_mul_left]


/-- Combined-index Cauchy product. -/
def convolution {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) (k : ℕ) : R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, f ij.1 * g ij.2

/-- Adding one reciprocal factor increases the polynomial coefficient weight by one.
This proves the counting estimate in Lemma 5(a) without using eigenvalue-defined polynomials. -/
theorem convolution_coefficient_bound {R : Type*} [NormedRing R]
    (f g : ℕ → R) (ν k : ℕ) (ρ A B : ℝ) (hp : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ A * ((i + 1 : ℕ) : ℝ) ^ ν * ρ ^ i)
    (hg : ∀ j : ℕ, ‖g j‖ ≤ B * ρ ^ j) :
    ‖convolution f g k‖ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ (ν + 1) * ρ ^ k := by
  have hterm (ij : ℕ × ℕ) (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal k) :
      ‖f ij.1 * g ij.2‖ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by
    have he : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hle : ij.1 + 1 ≤ k + 1 := by omega
    have hpow : (((ij.1 + 1 : ℕ) : ℝ)) ^ ν ≤ ((k + 1 : ℕ) : ℝ) ^ ν :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle) ν
    have hnorm := (norm_mul_le (f ij.1) (g ij.2)).trans
      (mul_le_mul (hf ij.1) (hg ij.2) (norm_nonneg _) (by positivity))
    calc
      _ ≤ (A * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ ij.1) * (B * ρ ^ ij.2) := hnorm
      _ = A * B * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by rw [← he, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hB)) (pow_nonneg hp.le k)
  unfold convolution
  calc
    _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, ‖f ij.1 * g ij.2‖ := norm_sum_le _ _
    _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; rw [pow_succ]; ring

/-- Exact Cauchy product identity used for the scalar factors of Lemma 5(a). -/
theorem convolution_tsum {R : Type*} [NormedRing R] [CompleteSpace R]
    (f g : ℕ → R) (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun i => ‖g i‖)) :
    ∑' k : ℕ, convolution f g k = (∑' i : ℕ, f i) * ∑' j : ℕ, g j := by
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm


/-- Form a combined-index product, starting with a distinguished matrix-valued factor. -/
def addFactors {R : Type*} [NonUnitalNonAssocSemiring R] (f : ℕ → R) :
    List (ℕ → R) → ℕ → R
  | [] => f
  | g :: gs => convolution (addFactors f gs) g

/-- Coefficient bound for any finite number of reciprocal-type factors. -/
theorem addFactors_coefficient_bound {R : Type*} [NormedRing R]
    (f : ℕ → R) (gs : List (ℕ → R)) (ρ A B : ℝ) (hp : 0 < ρ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ k : ℕ, ‖f k‖ ≤ A * ρ ^ k)
    (hg : ∀ g ∈ gs, ∀ k : ℕ, ‖g k‖ ≤ B * ρ ^ k) (k : ℕ) :
    ‖addFactors f gs k‖ ≤ A * B ^ gs.length * ((k + 1 : ℕ) : ℝ) ^ gs.length * ρ ^ k := by
  induction gs generalizing k with
  | nil => simpa [addFactors] using hf k
  | cons g gs ih =>
    have ht : ∀ k : ℕ, ‖addFactors f gs k‖ ≤
        A * B ^ gs.length * ((k + 1 : ℕ) : ℝ) ^ gs.length * ρ ^ k := by
      intro k
      exact ih (fun q hq => hg q (List.mem_cons_of_mem g hq)) k
    have hh := convolution_coefficient_bound (addFactors f gs) g gs.length k ρ
      (A * B ^ gs.length) B hp (by positivity) hB ht (hg g (List.mem_cons_self ..))
    change ‖convolution (addFactors f gs) g k‖ ≤ _
    convert hh using 1
    simp only [List.length_cons, pow_succ]
    ring

/-- The complete combined-index truncation estimate once individual coefficient estimates
are established. The matrix determinant polynomial identity remains a separate paper obligation. -/
theorem combined_index_truncation_bound {R : Type*} [NormedRing R] [CompleteSpace R]
    (f : ℕ → R) (gs : List (ℕ → R)) (ρ : ℝ) (hp : 0 < ρ) (h1 : ρ < 1)
    (hf : ∀ k : ℕ, ‖f k‖ ≤ 2 * ρ ^ k)
    (hg : ∀ g ∈ gs, ∀ k : ℕ, ‖g k‖ ≤ 2 * ρ ^ k) (m : ℕ) :
    ‖(∑' k : ℕ, addFactors f gs k) - ∑ k ∈ Finset.range (m + 1), addFactors f gs k‖ ≤
      2 ^ (gs.length + 1) * ((m + 1 : ℕ) : ℝ) ^ gs.length * ρ ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ gs.length * ρ ^ k := by
  apply series_truncation_bound (addFactors f gs) gs.length m ρ
    (2 ^ (gs.length + 1)) hp h1 (by positivity)
  intro k
  have h := addFactors_coefficient_bound f gs ρ 2 2 hp (by norm_num) (by norm_num) hf hg k
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

end RoughRegime.SeriesBounds
