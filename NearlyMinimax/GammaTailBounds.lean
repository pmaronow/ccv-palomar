module

public import NearlyMinimax.GaussianSpatialDomination


@[expose] public section

/-! Genuine Gamma moments and polynomial-exponential tail integrals. These
are the analytic ingredients for the log-scale simplex tail in the spatial
interpolation construction. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- The actual Gamma moment, with respect to Lebesgue measure on the positive
half-line. -/
theorem gamma_monomial_integrable {b : ℝ} (hb : 0 < b) (r : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ r * Real.exp (-(b * v))) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (r : ℝ)) (p := 1)
    (b := b) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg r)) (by norm_num) hb
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using h

theorem gamma_monomial_integral {b : ℝ} (hb : 0 < b) (r : ℕ) :
    (∫ v : ℝ in Ici 0, v ^ r * Real.exp (-(b * v))) =
      (r.factorial : ℝ) / b ^ (r + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (r : ℝ) + 1)
    (r := b) (by positivity) hb
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [h]
  have he : (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_natCast]
  rw [div_pow, one_pow]
  field_simp

/-- Translation of a genuine set integral; no integrability premise is
needed to identify the two Bochner integrals. -/
theorem integral_Ici_translate (A : ℝ) (f : ℝ → ℝ) :
    (∫ v : ℝ in Ici 0, f (A + v)) = ∫ u : ℝ in Ici A, f u := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage
    (s := Ici A) measurableSet_Ici
  have hs : (fun v : ℝ => A + v) ⁻¹' Ici A = Ici 0 := by
    ext v
    simp only [mem_preimage, mem_Ici]
    constructor <;> intro h <;> linarith
  rw [hs] at hp
  exact hp.integral_comp (MeasurableEquiv.addLeft A).measurableEmbedding f

theorem gamma_translated_monomial_integrable {b : ℝ} (hb : 0 < b)
    (A : ℝ) (m : ℕ) :
    IntegrableOn (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * v))) (Ici 0) := by
  have he : (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * v))) =
      fun v => ∑ l ∈ Finset.range (m + 1),
        (A ^ l * (m.choose l : ℝ)) * (v ^ (m - l) * Real.exp (-(b * v))) := by
    funext v
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  exact integrable_finsetSum _ fun l _ => (gamma_monomial_integrable hb (m - l)).const_mul _

/-- Exact exponential tail of an integer-shape Gamma density. The right-hand
side is a finite polynomial, derived by translation and the binomial theorem. -/
theorem gamma_polynomial_tail_integral {b : ℝ} (hb : 0 < b) (A : ℝ) (m : ℕ) :
    (∫ u : ℝ in Ici A, u ^ m * Real.exp (-(b * u)) / (m.factorial : ℝ)) =
      Real.exp (-(b * A)) *
        ∑ l ∈ Finset.range (m + 1), A ^ l / ((l.factorial : ℝ) * b ^ (m + 1 - l)) := by
  rw [← integral_Ici_translate A]
  have he : (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * (A + v))) / (m.factorial : ℝ)) =
      fun v => (Real.exp (-(b * A)) / (m.factorial : ℝ)) *
        ∑ l ∈ Finset.range (m + 1),
          (A ^ l * (m.choose l : ℝ)) * (v ^ (m - l) * Real.exp (-(b * v))) := by
    funext v
    rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add,
      add_pow, Finset.sum_mul, Finset.sum_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_const_mul, integral_finsetSum _ (fun l _ =>
    (gamma_monomial_integrable hb (m - l)).const_mul _)]
  simp_rw [integral_const_mul, gamma_monomial_integral hb]
  rw [div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have hlm : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hfl : (l.factorial : ℝ) ≠ 0 := by positivity
  have hfr : ((m - l).factorial : ℝ) ≠ 0 := by positivity
  have hp : b ≠ 0 := ne_of_gt hb
  have hchoose := Nat.cast_choose ℝ hlm
  rw [hchoose]
  have hn : m + 1 - l = (m - l) + 1 := by omega
  rw [hn]
  field_simp

/-- The original tail integrand is genuinely integrable, including at an
arbitrary translated boundary. -/
theorem gamma_polynomial_tail_integrable {b : ℝ} (hb : 0 < b) (A : ℝ) (m : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ m * Real.exp (-(b * u)) / (m.factorial : ℝ))
      (Ici A) := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage
    (s := Ici A) measurableSet_Ici
  have hs : (fun v : ℝ => A + v) ⁻¹' Ici A = Ici 0 := by
    ext v
    simp only [mem_preimage, mem_Ici]
    constructor <;> intro h <;> linarith
  rw [hs] at hp
  apply (hp.integrable_comp_emb (MeasurableEquiv.addLeft A).measurableEmbedding).mp
  have h := (gamma_translated_monomial_integrable hb A m).const_mul
    (Real.exp (-(b * A)) / (m.factorial : ℝ))
  convert h using 1
  funext v
  simp only [Function.comp_apply]
  rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add]
  ring

/-- A uniform polynomial-times-exponential Gamma tail bound, valid for every
integer shape and every rate at least one half. -/
theorem gamma_polynomial_tail_le {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b)
    (hA : 0 ≤ A) (m : ℕ) :
    (∫ u : ℝ in Ici A, u ^ m * Real.exp (-(b * u)) / (m.factorial : ℝ)) ≤
      6 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  rw [gamma_polynomial_tail_integral hbpos]
  have hinv : 1 / b ≤ (2 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb
  have hsum :
      (∑ l ∈ Finset.range (m + 1), A ^ l / ((l.factorial : ℝ) * b ^ (m + 1 - l))) ≤
        ((1 + A) ^ m * 2 ^ (m + 1)) * Real.exp 1 := by
    calc
      _ ≤ ∑ l ∈ Finset.range (m + 1),
          ((1 + A) ^ m * 2 ^ (m + 1)) * ((1 : ℝ) ^ l / (l.factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlm : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        have he : m + 1 - l ≤ m + 1 := Nat.sub_le _ _
        have hpowA : A ^ l ≤ (1 + A) ^ m :=
          (pow_le_pow_left₀ hA (by linarith) l).trans
            (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + A) hlm)
        have hpowB : (1 / b) ^ (m + 1 - l) ≤ (2 : ℝ) ^ (m + 1) :=
          (pow_le_pow_left₀ (by positivity) hinv _).trans
            (pow_le_pow_right₀ (by norm_num) he)
        have hmul := mul_le_mul hpowA hpowB (by positivity : 0 ≤ (1 / b) ^ (m + 1 - l))
          (by positivity : 0 ≤ (1 + A) ^ m)
        have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ (l.factorial : ℝ))
        convert hdiv using 1 <;> simp only [one_pow, div_pow] <;> ring
      _ = ((1 + A) ^ m * 2 ^ (m + 1)) *
          ∑ l ∈ Finset.range (m + 1), (1 : ℝ) ^ l / (l.factorial : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by norm_num) _)
        (by positivity)
  have hthree : (3 : ℝ) ≤ 3 ^ (m + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega : 1 ≤ m + 1)
    simpa using h
  have hconst : (2 : ℝ) ^ (m + 1) * Real.exp 1 ≤ 6 ^ (m + 1) := by
    calc
      _ ≤ 2 ^ (m + 1) * 3 := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (by positivity)
      _ ≤ 2 ^ (m + 1) * 3 ^ (m + 1) := mul_le_mul_of_nonneg_left
        hthree (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hfirst := mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg (-(b * A)))
  have hsecond := mul_le_mul_of_nonneg_right hconst
    (by positivity : 0 ≤ Real.exp (-(b * A)) * (1 + A) ^ m)
  calc
    _ ≤ _ := hfirst
    _ ≤ _ := by nlinarith [hsecond]

end NearlyMinimax
