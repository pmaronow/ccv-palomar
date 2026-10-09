module

public import Mathlib


@[expose] public section

/-!
# Lower-bound ingredients from Section 5

This file proves finite-space probability and algebraic ingredients of the
testing argument. It does not assert the marked Poisson comparison or the
asymptotic reduction proposition, whose infinite-dimensional hypotheses are
not represented by these finite-space definitions.
-/

namespace RoughRegime.Lower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

def sign (s : Bool) : ℝ := if s then 1 else -1

def signWeight (c : ℝ) (s t : Bool) : ℝ :=
  (1 + sign s * sign t * c) / 4

theorem signWeight_nonneg {c : ℝ} (hc : |c| ≤ 1) (s t : Bool) :
    0 ≤ signWeight c s t := by
  have hc' := abs_le.mp hc
  cases s <;> cases t <;> simp [signWeight, sign] <;> linarith

theorem signWeight_sum (c : ℝ) :
    (∑ s : Bool, ∑ t : Bool, signWeight c s t) = 1 := by
  simp [signWeight, sign]
  ring

theorem signWeight_simultaneous_flip (c : ℝ) (s t : Bool) :
    signWeight c (!s) (!t) = signWeight c s t := by
  cases s <;> cases t <;> simp [signWeight, sign]

theorem signWeight_second_flip (c : ℝ) (s t : Bool) :
    signWeight c s (!t) = signWeight (-c) s t := by
  cases s <;> cases t <;> simp [signWeight, sign]

def signMoment (c : ℝ) (ku kv : ℕ) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, signWeight c s t * sign s ^ ku * sign t ^ kv

theorem signMoment_difference (c : ℝ) (ku kv : ℕ) :
    signMoment c ku kv - signMoment (-c) ku kv =
      c / 2 * (1 - (-1 : ℝ) ^ ku) * (1 - (-1 : ℝ) ^ kv) := by
  simp [signMoment, signWeight, sign]
  ring

/-- The parity selection rule in equation (5.3), before averaging over phases. -/
theorem signMoment_difference_parity (c : ℝ) (ku kv : ℕ) :
    signMoment c ku kv - signMoment (-c) ku kv =
      if Odd ku ∧ Odd kv then 2 * c else 0 := by
  rw [signMoment_difference, neg_one_pow_eq_ite, neg_one_pow_eq_ite]
  rcases Nat.even_or_odd ku with hu | hu <;>
    rcases Nat.even_or_odd kv with hv | hv <;>
    simp [hu, hv, Nat.not_odd_iff_even.mpr, Nat.not_even_iff_odd.mpr] <;> ring

theorem signMoment_correlation (c : ℝ) : signMoment c 1 1 = c := by
  simp [signMoment, signWeight, sign]
  ring

theorem signMoment_first_marginal (c : ℝ) : signMoment c 1 0 = 0 := by
  simp [signMoment, signWeight, sign]
  ring

theorem signMoment_second_marginal (c : ℝ) : signMoment c 0 1 = 0 := by
  simp [signMoment, signWeight, sign]

/-- Equation (5.3) after averaging the conditional sign law over an arbitrary
phase/auxiliary-parameter measure. In particular, the phase space may be
continuous. The integrability hypotheses make the two prior expectations real. -/
theorem phase_sign_difference {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (c f : Ω → ℝ) (ku kv : ℕ)
    (hplus : MeasureTheory.Integrable (fun ω => signMoment (c ω) ku kv * f ω) μ)
    (hminus : MeasureTheory.Integrable (fun ω => signMoment (-c ω) ku kv * f ω) μ) :
    (∫ ω, signMoment (c ω) ku kv * f ω ∂μ) -
      (∫ ω, signMoment (-c ω) ku kv * f ω ∂μ) =
        if Odd ku ∧ Odd kv then 2 * ∫ ω, c ω * f ω ∂μ else 0 := by
  rw [← MeasureTheory.integral_sub hplus hminus]
  simp_rw [← sub_mul, signMoment_difference_parity]
  by_cases hp : Odd ku ∧ Odd kv
  · simp [hp, mul_assoc, MeasureTheory.integral_const_mul]
  · simp [hp]

/-- A probability distribution on a finite space, with real-valued masses. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

variable {α β : Type*} [Fintype α] [Fintype β]

def FiniteLaw.event (P : FiniteLaw α) (A : α → Prop) [DecidablePred A] : ℝ :=
  ∑ x, if A x then P.mass x else 0

def totalVariation (P Q : FiniteLaw α) : ℝ :=
  (∑ x, |P.mass x - Q.mass x|) / 2

def hellingerSquared (P Q : FiniteLaw α) : ℝ :=
  ∑ x, (Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)) ^ 2

def affinity (P Q : FiniteLaw α) : ℝ :=
  ∑ x, Real.sqrt (P.mass x) * Real.sqrt (Q.mass x)

theorem hellingerSquared_nonneg (P Q : FiniteLaw α) :
    0 ≤ hellingerSquared P Q := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem hellingerSquared_eq (P Q : FiniteLaw α) :
    hellingerSquared P Q = 2 - 2 * affinity P Q := by
  have hx (x : α) :
      (Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)) ^ 2 =
        P.mass x + Q.mass x - 2 * (Real.sqrt (P.mass x) * Real.sqrt (Q.mass x)) := by
    nlinarith [Real.sq_sqrt (P.nonneg x), Real.sq_sqrt (Q.nonneg x)]
  simp_rw [hellingerSquared, hx]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    P.total, Q.total, affinity]
  norm_num

theorem affinity_nonneg (P Q : FiniteLaw α) : 0 ≤ affinity P Q := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem affinity_le_one (P Q : FiniteLaw α) : affinity P Q ≤ 1 := by
  have := hellingerSquared_nonneg P Q
  rw [hellingerSquared_eq] at this
  linarith

theorem FiniteLaw.event_nonneg (P : FiniteLaw α) (A : α → Prop)
    [DecidablePred A] : 0 ≤ P.event A := by
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [P.nonneg x]

theorem FiniteLaw.event_mono (P : FiniteLaw α) {A B : α → Prop}
    [DecidablePred A] [DecidablePred B] (h : ∀ x, A x → B x) :
    P.event A ≤ P.event B := by
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x
  · simp [ha, h x ha]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> simp [P.nonneg x]

theorem FiniteLaw.event_complement (P : FiniteLaw α) (A : α → Prop)
    [DecidablePred A] : P.event (fun x => ¬ A x) = 1 - P.event A := by
  have hx (x : α) : (if ¬ A x then P.mass x else 0) =
      P.mass x - (if A x then P.mass x else 0) := by
    by_cases h : A x <;> simp [h]
  simp_rw [FiniteLaw.event, hx]
  rw [Finset.sum_sub_distrib, P.total]

theorem event_difference_le_tv (P Q : FiniteLaw α) (A : α → Prop)
    [DecidablePred A] : |P.event A - Q.event A| ≤ totalVariation P Q := by
  have hd : ∑ x, (P.mass x - Q.mass x) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, Q.total]
    ring
  have he : P.event A - Q.event A =
      ∑ x, if A x then P.mass x - Q.mass x else 0 := by
    simp only [FiniteLaw.event, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : A x <;> simp [h]
  rw [he, abs_le]
  constructor
  · have hh : (∑ x, -( |P.mass x - Q.mass x| - (P.mass x - Q.mass x)) / 2) ≤
        ∑ x, if A x then P.mass x - Q.mass x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      have ha := le_abs_self (P.mass x - Q.mass x)
      have hb := neg_le_abs (P.mass x - Q.mass x)
      split_ifs <;> linarith
    simpa [totalVariation, ← Finset.sum_div, Finset.sum_neg_distrib,
      Finset.sum_sub_distrib, hd, neg_div] using hh
  · have hh : (∑ x, if A x then P.mass x - Q.mass x else 0) ≤
        ∑ x, (|P.mass x - Q.mass x| + (P.mass x - Q.mass x)) / 2 := by
      apply Finset.sum_le_sum
      intro x _
      have ha := le_abs_self (P.mass x - Q.mass x)
      have hb := neg_le_abs (P.mass x - Q.mass x)
      split_ifs <;> linarith
    simpa [totalVariation, ← Finset.sum_div, Finset.sum_add_distrib, hd] using hh

/-- Sum of the two errors of a finite-space test is at least `1 - TV`. -/
theorem test_error_lower (P Q : FiniteLaw α) (A : α → Prop)
    [DecidablePred A] :
    1 - totalVariation P Q ≤ P.event (fun x => ¬ A x) + Q.event A := by
  have h := (abs_le.mp (event_difference_le_tv P Q A)).2
  rw [P.event_complement A]
  linarith

def FiniteLaw.prod (P : FiniteLaw α) (Q : FiniteLaw β) : FiniteLaw (α × β) where
  mass x := P.mass x.1 * Q.mass x.2
  nonneg x := mul_nonneg (P.nonneg _) (Q.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [P.total, Q.total]

theorem affinity_product (P₁ Q₁ : FiniteLaw α) (P₂ Q₂ : FiniteLaw β) :
    affinity (P₁.prod P₂) (Q₁.prod Q₂) = affinity P₁ Q₁ * affinity P₂ Q₂ := by
  unfold affinity FiniteLaw.prod
  simp_rw [Real.sqrt_mul (P₁.nonneg _), Real.sqrt_mul (Q₁.nonneg _)]
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ a b : ℝ, ∀ c d : ℝ, a * b * (c * d) = (a * c) * (b * d) by
    intros; ring]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem hellingerSquared_product_le (P₁ Q₁ : FiniteLaw α)
    (P₂ Q₂ : FiniteLaw β) :
    hellingerSquared (P₁.prod P₂) (Q₁.prod Q₂) ≤
      hellingerSquared P₁ Q₁ + hellingerSquared P₂ Q₂ := by
  rw [hellingerSquared_eq, affinity_product,
    hellingerSquared_eq, hellingerSquared_eq]
  have h₁ := affinity_le_one P₁ Q₁
  have h₂ := affinity_le_one P₂ Q₂
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]

theorem totalVariation_nonneg (P Q : FiniteLaw α) : 0 ≤ totalVariation P Q := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem totalVariation_sq_le_hellingerSquared (P Q : FiniteLaw α) :
    totalVariation P Q ^ 2 ≤ hellingerSquared P Q := by
  let f : α → ℝ := fun x => |Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)|
  let g : α → ℝ := fun x => Real.sqrt (P.mass x) + Real.sqrt (Q.mass x)
  have hfg (x : α) : f x * g x = |P.mass x - Q.mass x| := by
    have hs : 0 ≤ g x := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [← abs_of_nonneg hs, ← abs_mul]
    congr 1
    dsimp [f, g]
    nlinarith [Real.sq_sqrt (P.nonneg x), Real.sq_sqrt (Q.nonneg x)]
  have hf : (∑ x, f x ^ 2) = hellingerSquared P Q := by
    simp [f, hellingerSquared, sq_abs]
  have hg : (∑ x, g x ^ 2) = 2 + 2 * affinity P Q := by
    have hx (x : α) : g x ^ 2 = P.mass x + Q.mass x +
        2 * (Real.sqrt (P.mass x) * Real.sqrt (Q.mass x)) := by
      dsimp [g]
      nlinarith [Real.sq_sqrt (P.nonneg x), Real.sq_sqrt (Q.nonneg x)]
    simp_rw [hx]
    simp [Finset.sum_add_distrib, Finset.mul_sum, P.total, Q.total, affinity]
    norm_num
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) f g
  simp_rw [hfg] at hcs
  rw [hf, hg] at hcs
  have ht : (∑ x, |P.mass x - Q.mass x|) = 2 * totalVariation P Q := by
    unfold totalVariation
    ring
  rw [ht] at hcs
  have hh := hellingerSquared_nonneg P Q
  have ha := affinity_le_one P Q
  nlinarith [mul_nonneg hh (sub_nonneg.mpr ha)]

theorem totalVariation_le_hellinger (P Q : FiniteLaw α) :
    totalVariation P Q ≤ Real.sqrt (hellingerSquared P Q) := by
  have h := totalVariation_sq_le_hellingerSquared P Q
  have htv := totalVariation_nonneg P Q
  have hs := Real.sqrt_nonneg (hellingerSquared P Q)
  have hsq := Real.sq_sqrt (hellingerSquared_nonneg P Q)
  nlinarith

/-- The probability conclusion of the two-point argument for finite experiments. -/
theorem two_point_large_error (P Q : FiniteLaw α) (a b : ℝ) (_hab : a < b)
    (g : α → ℝ) (htv : totalVariation P Q ≤ 1 / 2) :
    (1 / 4 ≤ P.event (fun x => (b - a) / 2 ≤ |g x - a|)) ∨
      (1 / 4 ≤ Q.event (fun x => (b - a) / 2 ≤ |g x - b|)) := by
  classical
  have hp : P.event (fun x => ¬ g x < (a + b) / 2) ≤
      P.event (fun x => (b - a) / 2 ≤ |g x - a|) := by
    apply P.event_mono
    intro x hx
    have hh := le_of_not_gt hx
    have ha := le_abs_self (g x - a)
    linarith
  have hq : Q.event (fun x => g x < (a + b) / 2) ≤
      Q.event (fun x => (b - a) / 2 ≤ |g x - b|) := by
    apply Q.event_mono
    intro x hx
    have ha := neg_le_abs (g x - b)
    linarith
  have ht := test_error_lower P Q (fun x => g x < (a + b) / 2)
  by_contra h
  push Not at h
  linarith

theorem totalVariation_symm (P Q : FiniteLaw α) : totalVariation P Q = totalVariation Q P := by
  simp [totalVariation, abs_sub_comm]

theorem two_point_absolute_large_error (P Q : FiniteLaw α) (a b : ℝ) (hab : a ≠ b)
    (g : α → ℝ) (htv : totalVariation P Q ≤ 1 / 2) :
    (1 / 4 ≤ P.event (fun x => |b - a| / 2 ≤ |g x - a|)) ∨
      (1 / 4 ≤ Q.event (fun x => |b - a| / 2 ≤ |g x - b|)) := by
  classical
  rcases lt_or_gt_of_ne hab with h | h
  · simpa [abs_of_pos (sub_pos.mpr h)] using two_point_large_error P Q a b h g htv
  · rw [totalVariation_symm] at htv
    have hh := two_point_large_error Q P b a h g htv
    rw [abs_of_neg (sub_neg.mpr h)]
    have he : -(b - a) = a - b := by ring
    rw [he]
    exact hh.symm

def mean (P : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ x, P.mass x * f x

def variance (P : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, P.mass x * (f x - mean P f) ^ 2

def meanSquaredLoss (P : FiniteLaw α) (g : α → ℝ) (target : ℝ) : ℝ :=
  ∑ x, P.mass x * (g x - target) ^ 2

theorem meanSquaredLoss_nonneg (P : FiniteLaw α) (g : α → ℝ) (target : ℝ) :
    0 ≤ meanSquaredLoss P g target := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (P.nonneg x) (sq_nonneg _)

theorem tail_bound_implies_rmse_bound (P : FiniteLaw α) (g : α → ℝ)
    (target δ : ℝ) (hδ : 0 ≤ δ)
    (hprob : 1 / 4 ≤ P.event (fun x => δ / 2 ≤ |g x - target|)) :
    δ / 4 ≤ Real.sqrt (meanSquaredLoss P g target) := by
  classical
  have hp (x : α) :
      (if δ / 2 ≤ |g x - target| then P.mass x else 0) * (δ / 2) ^ 2 ≤
        P.mass x * (g x - target) ^ 2 := by
    split_ifs with hx
    · apply mul_le_mul_of_nonneg_left _ (P.nonneg x)
      nlinarith [sq_abs (g x - target), abs_nonneg (g x - target)]
    · simpa using mul_nonneg (P.nonneg x) (sq_nonneg (g x - target))
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => hp x)
  rw [← Finset.sum_mul] at hs
  change P.event (fun x => δ / 2 ≤ |g x - target|) * (δ / 2) ^ 2 ≤
    meanSquaredLoss P g target at hs
  have hm := mul_le_mul_of_nonneg_right hprob (sq_nonneg (δ / 2))
  have hroot := Real.sqrt_nonneg (meanSquaredLoss P g target)
  have hsq := Real.sq_sqrt (meanSquaredLoss_nonneg P g target)
  nlinarith

theorem finite_chebyshev (P : FiniteLaw α) (f : α → ℝ) (r : ℝ) (hr : 0 < r) :
    P.event (fun x => r ≤ |f x - mean P f|) ≤ variance P f / r ^ 2 := by
  classical
  have hpoint (x : α) :
      (if r ≤ |f x - mean P f| then P.mass x else 0) * r ^ 2 ≤
        P.mass x * (f x - mean P f) ^ 2 := by
    split_ifs with hx
    · apply mul_le_mul_of_nonneg_left _ (P.nonneg x)
      nlinarith [sq_abs (f x - mean P f), abs_nonneg (f x - mean P f)]
    · simpa using mul_nonneg (P.nonneg x) (sq_nonneg (f x - mean P f))
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => hpoint x)
  rw [← Finset.sum_mul] at hsum
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr hsum

/-- The square-root inequality used for mixture likelihoods. -/
theorem square_root_difference_bound {f g c : ℝ} (hc : 0 < c)
    (hf : c ≤ f) (hg : c ≤ g) :
    (Real.sqrt f - Real.sqrt g) ^ 2 ≤ (f - g) ^ 2 / (4 * c) := by
  have hf0 : 0 ≤ f := le_trans (le_of_lt hc) hf
  have hg0 : 0 ≤ g := le_trans (le_of_lt hc) hg
  have hsfc := Real.sqrt_le_sqrt hf
  have hsgc := Real.sqrt_le_sqrt hg
  have hsc := Real.sqrt_nonneg c
  have hsf := Real.sqrt_nonneg f
  have hsg := Real.sqrt_nonneg g
  have hscc := Real.sq_sqrt (le_of_lt hc)
  have hsff := Real.sq_sqrt hf0
  have hsgg := Real.sq_sqrt hg0
  have hprod : c ≤ Real.sqrt f * Real.sqrt g := by
    nlinarith [mul_le_mul hsfc hsgc hsc hsf]
  have hden : 4 * c ≤ (Real.sqrt f + Real.sqrt g) ^ 2 := by nlinarith
  have hid : (f - g) ^ 2 =
      (Real.sqrt f - Real.sqrt g) ^ 2 * (Real.sqrt f + Real.sqrt g) ^ 2 := by
    have hi : f - g = (Real.sqrt f - Real.sqrt g) * (Real.sqrt f + Real.sqrt g) := by
      nlinarith
    rw [hi, mul_pow]
  apply (le_div_iff₀ (by positivity : 0 < 4 * c)).mpr
  rw [hid]
  exact mul_le_mul_of_nonneg_left hden (sq_nonneg _)

/-- An affine density path has quadratic Hellinger separation, in finite spaces. -/
theorem affine_hellinger_bound (P : FiniteLaw α) (f₀ f₁ : α → ℝ)
    (t s cf Cf : ℝ) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (ht : ∀ x, cf ≤ f₀ x + t * f₁ x)
    (hs : ∀ x, cf ≤ f₀ x + s * f₁ x)
    (hf₁ : ∀ x, |f₁ x| ≤ Cf) :
    (∑ x, P.mass x * (Real.sqrt (f₀ x + t * f₁ x) -
      Real.sqrt (f₀ x + s * f₁ x)) ^ 2) ≤ Cf ^ 2 * (t - s) ^ 2 / (4 * cf) := by
  have hx (x : α) :
      (Real.sqrt (f₀ x + t * f₁ x) - Real.sqrt (f₀ x + s * f₁ x)) ^ 2 ≤
        Cf ^ 2 * (t - s) ^ 2 / (4 * cf) := by
    have h := square_root_difference_bound hcf (ht x) (hs x)
    have hsq : f₁ x ^ 2 ≤ Cf ^ 2 := by
      nlinarith [sq_abs (f₁ x), abs_nonneg (f₁ x), hf₁ x]
    have hid : (f₀ x + t * f₁ x - (f₀ x + s * f₁ x)) ^ 2 =
        f₁ x ^ 2 * (t - s) ^ 2 := by ring
    rw [hid] at h
    exact le_trans h (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (by positivity))
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) =>
    mul_le_mul_of_nonneg_left (hx x) (P.nonneg x))
  simpa [← Finset.sum_mul, P.total] using hh

def FiniteLaw.mix (P Q : FiniteLaw α) (π : ℝ) (hπ₀ : 0 ≤ π) (hπ₁ : π ≤ 1) :
    FiniteLaw α where
  mass x := (1 - π) * P.mass x + π * Q.mass x
  nonneg x := add_nonneg (mul_nonneg (sub_nonneg.mpr hπ₁) (P.nonneg x))
    (mul_nonneg hπ₀ (Q.nonneg x))
  total := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, P.total, Q.total]

/-- Exact contamination identity used to pass from Poissonized to fixed-size data. -/
theorem totalVariation_common_contamination (P Q R : FiniteLaw α)
    (π : ℝ) (hπ₀ : 0 ≤ π) (hπ₁ : π ≤ 1) :
    totalVariation (P.mix R π hπ₀ hπ₁) (Q.mix R π hπ₀ hπ₁) =
      (1 - π) * totalVariation P Q := by
  have hx (x : α) : |(P.mix R π hπ₀ hπ₁).mass x -
      (Q.mix R π hπ₀ hπ₁).mass x| = (1 - π) * |P.mass x - Q.mass x| := by
    change |(1 - π) * P.mass x + π * R.mass x -
      ((1 - π) * Q.mass x + π * R.mass x)| = _
    rw [show (1 - π) * P.mass x + π * R.mass x -
      ((1 - π) * Q.mass x + π * R.mass x) = (1 - π) * (P.mass x - Q.mass x) by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr hπ₁)]
  unfold totalVariation
  simp_rw [hx]
  rw [← Finset.mul_sum]
  ring

/-- Appending the same independent random seed preserves total variation. -/
theorem totalVariation_common_product (P Q : FiniteLaw α) (R : FiniteLaw β) :
    totalVariation (P.prod R) (Q.prod R) = totalVariation P Q := by
  unfold totalVariation
  have hx (x : α × β) : |(P.prod R).mass x - (Q.prod R).mass x| =
      |P.mass x.1 - Q.mass x.1| * R.mass x.2 := by
    change |P.mass x.1 * R.mass x.2 - Q.mass x.1 * R.mass x.2| = _
    rw [← sub_mul, abs_mul, abs_of_nonneg (R.nonneg _)]
  simp_rw [hx]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp [R.total]

/-- The distribution of an `n`-tuple of independent observations. -/
def FiniteLaw.iid (P : FiniteLaw α) (n : ℕ) : FiniteLaw (Fin n → α) where
  mass xs := ∏ i, P.mass (xs i)
  nonneg xs := Finset.prod_nonneg fun i _ => P.nonneg (xs i)
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]

theorem sqrt_finite_product {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i, f i) = ∏ i, Real.sqrt (f i) := by
  apply (Real.sqrt_eq_iff_eq_sq (Finset.prod_nonneg fun i _ => hf i)
    (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg (f i))).mpr
  rw [← Finset.prod_pow]
  simp_rw [Real.sq_sqrt (hf _)]

theorem affinity_iid (P Q : FiniteLaw α) (n : ℕ) :
    affinity (P.iid n) (Q.iid n) = affinity P Q ^ n := by
  unfold affinity FiniteLaw.iid
  simp_rw [sqrt_finite_product _ (fun i => P.nonneg _),
    sqrt_finite_product _ (fun i => Q.nonneg _)]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro xs _
  rw [Finset.prod_mul_distrib]

theorem hellingerSquared_iid_le (P Q : FiniteLaw α) (n : ℕ) :
    hellingerSquared (P.iid n) (Q.iid n) ≤ n * hellingerSquared P Q := by
  rw [hellingerSquared_eq, affinity_iid, hellingerSquared_eq]
  have h := one_add_mul_sub_le_pow (by linarith [affinity_nonneg P Q] :
    -1 ≤ affinity P Q) n
  nlinarith

theorem affine_law_hellinger_bound (R P Q : FiniteLaw α) (f₀ f₁ : α → ℝ)
    (t s cf Cf : ℝ) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (ht : ∀ x, cf ≤ f₀ x + t * f₁ x) (hs : ∀ x, cf ≤ f₀ x + s * f₁ x)
    (hf₁ : ∀ x, |f₁ x| ≤ Cf)
    (hP : ∀ x, P.mass x = (f₀ x + t * f₁ x) * R.mass x)
    (hQ : ∀ x, Q.mass x = (f₀ x + s * f₁ x) * R.mass x) :
    hellingerSquared P Q ≤ Cf ^ 2 * (t - s) ^ 2 / (4 * cf) := by
  have he : hellingerSquared P Q =
      ∑ x, R.mass x * (Real.sqrt (f₀ x + t * f₁ x) -
        Real.sqrt (f₀ x + s * f₁ x)) ^ 2 := by
    unfold hellingerSquared
    apply Finset.sum_congr rfl
    intro x _
    rw [hP, hQ, Real.sqrt_mul (le_trans (le_of_lt hcf) (ht x)),
      Real.sqrt_mul (le_trans (le_of_lt hcf) (hs x)), ← sub_mul, mul_pow,
      Real.sq_sqrt (R.nonneg x)]
    ring
  rw [he]
  exact affine_hellinger_bound R f₀ f₁ t s cf Cf hcf hCf ht hs hf₁

/-- A nonzero derivative gives the symmetric target separation used in Lemma 10.
The assertion is local on punctured neighborhoods, with its actual derivative
assumption, rather than a supplied separation hypothesis. -/
theorem derivative_symmetric_separation {F : ℝ → ℝ} {t₀ D : ℝ}
    (hF : HasDerivAt F D t₀) (hD : D ≠ 0) :
    ∀ᶠ h in nhdsWithin (0 : ℝ) ({0}ᶜ),
      |D| * |h| ≤ |F (t₀ + h) - F (t₀ - h)| := by
  have hp : HasDerivAt (fun h : ℝ => F (t₀ + h)) D 0 := by
    have hF' : HasDerivAt F D (t₀ + id 0) := by simpa using hF
    simpa [Function.comp_def] using hF'.comp 0 ((hasDerivAt_id 0).const_add t₀)
  have hm : HasDerivAt (fun h : ℝ => F (t₀ - h)) (-D) 0 := by
    have hF' : HasDerivAt F D (t₀ - id 0) := by simpa using hF
    simpa [Function.comp_def] using hF'.comp 0 ((hasDerivAt_id 0).const_sub t₀)
  have hg : HasDerivAt (fun h : ℝ => F (t₀ + h) - F (t₀ - h)) (2 * D) 0 := by
    convert hp.sub hm using 1; ring
  have hs : Filter.Tendsto (fun h : ℝ => |(F (t₀ + h) - F (t₀ - h)) / h|)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds |2 * D|) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hg.tendsto_slope_zero.abs
  have hd0 : 0 < |D| := abs_pos.mpr hD
  have hgap : |D| < |2 * D| := by rw [abs_mul]; norm_num; linarith
  filter_upwards [hs.eventually (eventually_gt_nhds hgap),
    self_mem_nhdsWithin] with h hh hn
  have hn0 : h ≠ 0 := by simpa using hn
  rw [abs_div] at hh
  have habs : 0 < |h| := abs_pos.mpr hn0
  exact le_of_lt ((lt_div_iff₀ habs).mp hh)

/-- Finite-experiment affine-path testing theorem, with the differentiability
assumption of Lemma 10. The local scale condition becomes a constant condition
when `h = a / sqrt n`; the event bound is uniform over all estimators. -/
theorem finite_affine_path_local_testing (R : FiniteLaw α)
    (P : ℝ → FiniteLaw α) (f₀ f₁ : α → ℝ) (F : ℝ → ℝ)
    (l r t₀ D cf Cf : ℝ) (ht₀ : t₀ ∈ Set.Ioo l r)
    (hF : HasDerivAt F D t₀) (hD : D ≠ 0) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hdens : ∀ t ∈ Set.Ioo l r, ∀ x, (P t).mass x = (f₀ x + t * f₁ x) * R.mass x)
    (hpos : ∀ t ∈ Set.Ioo l r, ∀ x, cf ≤ f₀ x + t * f₁ x)
    (hscore : ∀ x, |f₁ x| ≤ Cf) :
    ∀ᶠ h in nhdsWithin (0 : ℝ) ({0}ᶜ), ∀ n : ℕ,
      (n : ℝ) * Cf ^ 2 * h ^ 2 / cf ≤ 1 / 4 → ∀ g : (Fin n → α) → ℝ,
        ∃ t ∈ Set.Ioo l r,
          1 / 4 ≤ ((P t).iid n).event (fun xs => |D| * |h| / 2 ≤ |g xs - F t|) := by
  classical
  have hJ : Set.Ioo l r ∈ nhds t₀ := isOpen_Ioo.mem_nhds ht₀
  have hplus : ∀ᶠ h in nhds (0 : ℝ), t₀ + h ∈ Set.Ioo l r := by
    have ht : Filter.Tendsto (fun h : ℝ => t₀ + h) (nhds 0) (nhds t₀) := by
      simpa using tendsto_const_nhds.add (Filter.tendsto_id : Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0))
    exact ht.eventually hJ
  have hminus : ∀ᶠ h in nhds (0 : ℝ), t₀ - h ∈ Set.Ioo l r := by
    have ht : Filter.Tendsto (fun h : ℝ => t₀ - h) (nhds 0) (nhds t₀) := by
      simpa using tendsto_const_nhds.sub (Filter.tendsto_id : Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0))
    exact ht.eventually hJ
  filter_upwards [derivative_symmetric_separation hF hD,
    hplus.filter_mono nhdsWithin_le_nhds, hminus.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with h hsep hp hm hn
  intro n hsmall g
  have hn0 : h ≠ 0 := by simpa using hn
  have hpossep : 0 < |D| * |h| := mul_pos (abs_pos.mpr hD) (abs_pos.mpr hn0)
  have htargets : F (t₀ + h) ≠ F (t₀ - h) := by
    intro he
    rw [he, sub_self, abs_zero] at hsep
    linarith
  have hb := affine_law_hellinger_bound R (P (t₀ + h)) (P (t₀ - h)) f₀ f₁
    (t₀ + h) (t₀ - h) cf Cf hcf hCf (hpos _ hp) (hpos _ hm) hscore
    (hdens _ hp) (hdens _ hm)
  have hh := hellingerSquared_iid_le (P (t₀ + h)) (P (t₀ - h)) n
  have hi : hellingerSquared ((P (t₀ + h)).iid n) ((P (t₀ - h)).iid n) ≤ 1 / 4 := by
    have hscale : (n : ℝ) * (Cf ^ 2 * (t₀ + h - (t₀ - h)) ^ 2 / (4 * cf)) =
        (n : ℝ) * Cf ^ 2 * h ^ 2 / cf := by ring
    calc
      _ ≤ (n : ℝ) * hellingerSquared (P (t₀ + h)) (P (t₀ - h)) := hh
      _ ≤ (n : ℝ) * (Cf ^ 2 * (t₀ + h - (t₀ - h)) ^ 2 / (4 * cf)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
      _ = (n : ℝ) * Cf ^ 2 * h ^ 2 / cf := hscale
      _ ≤ 1 / 4 := hsmall
  have htv : totalVariation ((P (t₀ + h)).iid n) ((P (t₀ - h)).iid n) ≤ 1 / 2 := by
    have hs := totalVariation_sq_le_hellingerSquared ((P (t₀ + h)).iid n) ((P (t₀ - h)).iid n)
    nlinarith [totalVariation_nonneg ((P (t₀ + h)).iid n) ((P (t₀ - h)).iid n)]
  have ht := two_point_absolute_large_error ((P (t₀ + h)).iid n) ((P (t₀ - h)).iid n)
    (F (t₀ + h)) (F (t₀ - h)) htargets g htv
  rw [abs_sub_comm (F (t₀ - h)) (F (t₀ + h))] at ht
  rcases ht with ht | ht
  · refine ⟨t₀ + h, hp, le_trans ht ?_⟩
    apply FiniteLaw.event_mono
    intro xs hx
    linarith
  · refine ⟨t₀ - h, hm, le_trans ht ?_⟩
    apply FiniteLaw.event_mono
    intro xs hx
    linarith

/-- Root-`n` two-point lower bound for a finite affine density family.
This is a finite-space specialization of Lemma 10, proved from density and
derivative hypotheses. The use of `n + 1` avoids a vacuous division at `n = 0`. -/
theorem finite_affine_path_rootn (R : FiniteLaw α)
    (P : ℝ → FiniteLaw α) (f₀ f₁ : α → ℝ) (F : ℝ → ℝ)
    (l r t₀ D cf Cf a : ℝ) (ht₀ : t₀ ∈ Set.Ioo l r)
    (hF : HasDerivAt F D t₀) (hD : D ≠ 0) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (ha : 0 < a) (hsmall : Cf ^ 2 * a ^ 2 / cf ≤ 1 / 4)
    (hdens : ∀ t ∈ Set.Ioo l r, ∀ x, (P t).mass x = (f₀ x + t * f₁ x) * R.mass x)
    (hpos : ∀ t ∈ Set.Ioo l r, ∀ x, cf ≤ f₀ x + t * f₁ x)
    (hscore : ∀ x, |f₁ x| ≤ Cf) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ g : (Fin n → α) → ℝ,
      ∃ t ∈ Set.Ioo l r,
        (1 / 4 ≤ ((P t).iid n).event (fun xs =>
          |D| * (a / Real.sqrt ((n + 1 : ℕ) : ℝ)) / 2 ≤ |g xs - F t|)) ∧
        (|D| * (a / Real.sqrt ((n + 1 : ℕ) : ℝ)) / 4 ≤
          Real.sqrt (meanSquaredLoss ((P t).iid n) g (F t))) := by
  classical
  let h : ℕ → ℝ := fun n => a / Real.sqrt ((n + 1 : ℕ) : ℝ)
  have hposn (n : ℕ) : 0 < h n := by
    dsimp [h]
    exact div_pos ha (Real.sqrt_pos.mpr (by positivity))
  have ht : Filter.Tendsto h Filter.atTop (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
      have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hc)
      simpa [h, div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    · exact Filter.Eventually.of_forall fun n => by simpa using ne_of_gt (hposn n)
  have hlocal := finite_affine_path_local_testing R P f₀ f₁ F l r t₀ D cf Cf ht₀
    hF hD hcf hCf hdens hpos hscore
  filter_upwards [ht.eventually hlocal] with n hn
  intro g
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hscale : (n : ℝ) * h n ^ 2 ≤ a ^ 2 := by
    dsimp [h]
    rw [div_pow, Real.sq_sqrt (le_of_lt hn1), ← mul_div_assoc]
    apply (div_le_iff₀ hn1).mpr
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg a]
  have hc : (n : ℝ) * Cf ^ 2 * h n ^ 2 / cf ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_left hscale (sq_nonneg Cf)
    have hd := div_le_div_of_nonneg_right hm (le_of_lt hcf)
    have he : Cf ^ 2 * ((n : ℝ) * h n ^ 2) = (n : ℝ) * Cf ^ 2 * h n ^ 2 := by ring
    rw [he] at hd
    exact le_trans hd hsmall
  obtain ⟨t, hJ, he⟩ := hn n hc g
  rw [abs_of_pos (hposn n)] at he
  refine ⟨t, hJ, he, ?_⟩
  exact tail_bound_implies_rmse_bound ((P t).iid n) g (F t) (|D| * h n)
    (mul_nonneg (abs_nonneg D) (le_of_lt (hposn n))) he

theorem exists_small_parametric_amplitude (cf Cf : ℝ) :
    ∃ a : ℝ, 0 < a ∧ Cf ^ 2 * a ^ 2 / cf ≤ 1 / 4 := by
  have hc : Continuous (fun a : ℝ => Cf ^ 2 * a ^ 2 / cf) := by fun_prop
  have ht : Filter.Tendsto (fun a : ℝ => Cf ^ 2 * a ^ 2 / cf) (nhds 0) (nhds 0) := by
    simpa using hc.tendsto 0
  have he := ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε / 2, by linarith, le_of_lt (hsub ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < ε / 2)]
  linarith

/-- Existential root-`n` RMSE conclusion of Lemma 10 on a finite observation space.
The constant is strictly positive and independent of the estimator and `n`. -/
theorem finite_parametric_testing_bound (R : FiniteLaw α)
    (P : ℝ → FiniteLaw α) (f₀ f₁ : α → ℝ) (F : ℝ → ℝ)
    (l r t₀ D cf Cf : ℝ) (ht₀ : t₀ ∈ Set.Ioo l r)
    (hF : HasDerivAt F D t₀) (hD : D ≠ 0) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hdens : ∀ t ∈ Set.Ioo l r, ∀ x, (P t).mass x = (f₀ x + t * f₁ x) * R.mass x)
    (hpos : ∀ t ∈ Set.Ioo l r, ∀ x, cf ≤ f₀ x + t * f₁ x)
    (hscore : ∀ x, |f₁ x| ≤ Cf) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ g : (Fin n → α) → ℝ,
      ∃ t ∈ Set.Ioo l r,
        c / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ Real.sqrt (meanSquaredLoss ((P t).iid n) g (F t)) := by
  obtain ⟨a, ha, hsmall⟩ := exists_small_parametric_amplitude cf Cf
  refine ⟨|D| * a / 4, by positivity, ?_⟩
  filter_upwards [finite_affine_path_rootn R P f₀ f₁ F l r t₀ D cf Cf a ht₀
    hF hD hcf hCf ha hsmall hdens hpos hscore] with n hn
  intro g
  obtain ⟨t, hJ, _, hbound⟩ := hn g
  refine ⟨t, hJ, ?_⟩
  have he : (|D| * a / 4) / Real.sqrt ((n + 1 : ℕ) : ℝ) =
      |D| * (a / Real.sqrt ((n + 1 : ℕ) : ℝ)) / 4 := by ring
  rw [he]
  exact hbound

theorem FiniteLaw.event_union_le (P : FiniteLaw α) (A B : α → Prop)
    [DecidablePred A] [DecidablePred B] :
    P.event (fun x => A x ∨ B x) ≤ P.event A + P.event B := by
  rw [FiniteLaw.event, FiniteLaw.event, FiniteLaw.event, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb, P.nonneg x]

/-- A finite Bayesian experiment: a prior and one data law for each parameter. -/
structure FiniteExperiment (β α : Type*) [Fintype β] [Fintype α] where
  prior : FiniteLaw β
  dataLaw : β → FiniteLaw α

def FiniteExperiment.joint (E : FiniteExperiment β α) : FiniteLaw (β × α) where
  mass x := E.prior.mass x.1 * (E.dataLaw x.1).mass x.2
  nonneg x := mul_nonneg (E.prior.nonneg _) ((E.dataLaw _).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteLaw.total, mul_one]
    exact E.prior.total

def FiniteExperiment.marginal (E : FiniteExperiment β α) : FiniteLaw α where
  mass x := ∑ θ, E.prior.mass θ * (E.dataLaw θ).mass x
  nonneg x := Finset.sum_nonneg fun θ _ =>
    mul_nonneg (E.prior.nonneg θ) ((E.dataLaw θ).nonneg x)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteLaw.total, mul_one]
    exact E.prior.total

theorem FiniteExperiment.joint_data_event (E : FiniteExperiment β α) (A : α → Prop)
    [DecidablePred A] : E.joint.event (fun x => A x.2) = E.marginal.event A := by
  unfold FiniteLaw.event FiniteExperiment.joint FiniteExperiment.marginal
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : A x <;> simp [h]

theorem FiniteExperiment.joint_parameter_event (E : FiniteExperiment β α)
    (A : β → Prop) [DecidablePred A] :
    E.joint.event (fun x => A x.1) = E.prior.event A := by
  unfold FiniteLaw.event FiniteExperiment.joint
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro θ _
  by_cases h : A θ <;> simp [h, ← Finset.mul_sum, (E.dataLaw θ).total]

theorem FiniteExperiment.error_le_of_uniform (E : FiniteExperiment β α)
    (g : α → ℝ) (target : β → ℝ) (δ r : ℝ)
    (hr : ∀ θ, (E.dataLaw θ).event (fun x => δ ≤ |g x - target θ|) ≤ r) :
    E.joint.event (fun x => δ ≤ |g x.2 - target x.1|) ≤ r := by
  classical
  have he : E.joint.event (fun x => δ ≤ |g x.2 - target x.1|) =
      ∑ θ, E.prior.mass θ * (E.dataLaw θ).event (fun x => δ ≤ |g x - target θ|) := by
    unfold FiniteLaw.event FiniteExperiment.joint
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro θ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [he]
  have hh := Finset.sum_le_sum (fun θ (_ : θ ∈ (Finset.univ : Finset β)) =>
    mul_le_mul_of_nonneg_left (hr θ) (E.prior.nonneg θ))
  simpa [← Finset.sum_mul, E.prior.total] using hh

/-- Finite-space two-fuzzy-hypotheses transfer, including its `3/8` constant.
The assumptions are quantitative TV and prior variance bounds; no lower-bound
conclusion is supplied as a hypothesis. -/
theorem fuzzy_testing_transfer (E₀ E₁ : FiniteExperiment β α)
    (target₀ target₁ : β → ℝ) (g : α → ℝ) (r : ℝ)
    (hsep : mean E₀.prior target₀ < mean E₁.prior target₁)
    (hsmall : totalVariation E₀.marginal E₁.marginal +
      variance E₀.prior target₀ / ((mean E₁.prior target₁ - mean E₀.prior target₀) / 4) ^ 2 +
      variance E₁.prior target₁ / ((mean E₁.prior target₁ - mean E₀.prior target₀) / 4) ^ 2 ≤ 1 / 4)
    (herr₀ : ∀ θ, (E₀.dataLaw θ).event (fun x =>
      (mean E₁.prior target₁ - mean E₀.prior target₀) / 4 ≤ |g x - target₀ θ|) ≤ r)
    (herr₁ : ∀ θ, (E₁.dataLaw θ).event (fun x =>
      (mean E₁.prior target₁ - mean E₀.prior target₀) / 4 ≤ |g x - target₁ θ|) ≤ r) :
    3 / 8 ≤ r := by
  classical
  let a := mean E₀.prior target₀
  let b := mean E₁.prior target₁
  let δ := (b - a) / 4
  have hδ : 0 < δ := by dsimp [δ, a, b]; linarith
  have hp : E₀.marginal.event (fun x => ¬ g x < (a + b) / 2) ≤
      r + variance E₀.prior target₀ / δ ^ 2 := by
    rw [← E₀.joint_data_event]
    have hi : E₀.joint.event (fun x => ¬ g x.2 < (a + b) / 2) ≤
        E₀.joint.event (fun x => δ ≤ |g x.2 - target₀ x.1| ∨
          δ ≤ |target₀ x.1 - a|) := by
      apply E₀.joint.event_mono
      intro x hx
      by_contra hn
      push Not at hn
      have hg := le_abs_self (g x.2 - target₀ x.1)
      have ht := le_abs_self (target₀ x.1 - a)
      dsimp [δ] at hn
      have hx' := le_of_not_gt hx
      linarith
    have hu := E₀.joint.event_union_le (fun x => δ ≤ |g x.2 - target₀ x.1|)
      (fun x => δ ≤ |target₀ x.1 - a|)
    have he := E₀.error_le_of_uniform g target₀ δ r herr₀
    have hc := finite_chebyshev E₀.prior target₀ δ hδ
    rw [← E₀.joint_parameter_event] at hc
    exact le_trans (le_trans hi hu) (add_le_add he hc)
  have hq : E₁.marginal.event (fun x => g x < (a + b) / 2) ≤
      r + variance E₁.prior target₁ / δ ^ 2 := by
    rw [← E₁.joint_data_event]
    have hi : E₁.joint.event (fun x => g x.2 < (a + b) / 2) ≤
        E₁.joint.event (fun x => δ ≤ |g x.2 - target₁ x.1| ∨
          δ ≤ |target₁ x.1 - b|) := by
      apply E₁.joint.event_mono
      intro x hx
      by_contra hn
      push Not at hn
      have hg := neg_le_abs (g x.2 - target₁ x.1)
      have ht := neg_le_abs (target₁ x.1 - b)
      dsimp [δ] at hn
      linarith
    have hu := E₁.joint.event_union_le (fun x => δ ≤ |g x.2 - target₁ x.1|)
      (fun x => δ ≤ |target₁ x.1 - b|)
    have he := E₁.error_le_of_uniform g target₁ δ r herr₁
    have hc := finite_chebyshev E₁.prior target₁ δ hδ
    rw [← E₁.joint_parameter_event] at hc
    exact le_trans (le_trans hi hu) (add_le_add he hc)
  have ht := test_error_lower E₀.marginal E₁.marginal (fun x => g x < (a + b) / 2)
  change totalVariation E₀.marginal E₁.marginal +
    variance E₀.prior target₀ / δ ^ 2 + variance E₁.prior target₁ / δ ^ 2 ≤ 1 / 4 at hsmall
  linarith

/-- Real masses of a Poisson count distribution. -/
def poissonMass (rate : ℝ) (n : ℕ) : ℝ := Real.exp (-rate) * rate ^ n / n.factorial

theorem poissonMass_nonneg (rate : ℝ) (hr : 0 ≤ rate) (n : ℕ) :
    0 ≤ poissonMass rate n := by
  unfold poissonMass
  positivity

theorem poissonMass_hasSum (rate : ℝ) : HasSum (poissonMass rate) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp rate).mul_left (Real.exp (-rate)) using 1
  · ext n
    simp [poissonMass, mul_div_assoc]
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    simp

/-- Poisson probability generating functional after conditioning on the count. -/
theorem poisson_generating_hasSum (rate h : ℝ) :
    HasSum (fun n => poissonMass rate n * h ^ n) (Real.exp (rate * (h - 1))) := by
  convert (NormedSpace.expSeries_div_hasSum_exp (rate * h)).mul_left
    (Real.exp (-rate)) using 1
  · ext n
    simp [poissonMass, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

/-- Exact finite marked-space version of the Poisson generating functional.
For `rate ≥ 0`, the Poisson masses define an actual count law; each mark has law `P`. -/
theorem finite_marked_poisson_generating_hasSum (P : FiniteLaw α) (rate : ℝ)
    (h : α → ℝ) :
    HasSum (fun n => poissonMass rate n *
      ∑ xs : Fin n → α, ∏ i, P.mass (xs i) * h (xs i))
      (Real.exp (rate * (mean P h - 1))) := by
  simpa [mean, Fintype.sum_pow] using poisson_generating_hasSum rate (mean P h)

/-- Expand the square of a finite signed mixture. -/
theorem finite_mixture_square (ν : β → ℝ) (f : β → ℝ) :
    (∑ ω, ν ω * f ω) ^ 2 = ∑ ω, ∑ ω', ν ω * ν ω' * f ω * f ω' := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ω' _
  ring

theorem weighted_mixture_square {γ : Type*} [Fintype γ]
    (ν : β → ℝ) (w : γ → ℝ) (f : β → γ → ℝ) :
    (∑ x, w x * (∑ ω, ν ω * f ω x) ^ 2) =
      ∑ ω, ∑ ω', ν ω * ν ω' * ∑ x, w x * f ω x * f ω' x := by
  simp_rw [finite_mixture_square, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω' _
  apply Finset.sum_congr rfl
  intro x _
  ring

def tensorMixture (ν : β → ℝ) (φ : β → α → ℝ) (k : ℕ) (xs : Fin k → α) : ℝ :=
  ∑ ω, ν ω * ∏ i, φ ω (xs i)

def weightedInner (w : α → ℝ) (φ : β → α → ℝ) (ω ω' : β) : ℝ :=
  ∑ x, w x * φ ω x * φ ω' x

def tensorNormSquared (w : α → ℝ) (ν : β → ℝ) (φ : β → α → ℝ) (k : ℕ) : ℝ :=
  ∑ xs : Fin k → α, (∏ i, w (xs i)) * tensorMixture ν φ k xs ^ 2

/-- Tensor Gram identity behind equation (5.8) in a finite marked space. -/
theorem tensorNormSquared_gram (w : α → ℝ) (ν : β → ℝ) (φ : β → α → ℝ)
    (k : ℕ) : tensorNormSquared w ν φ k =
      ∑ ω, ∑ ω', ν ω * ν ω' * weightedInner w φ ω ω' ^ k := by
  unfold tensorNormSquared tensorMixture
  rw [weighted_mixture_square]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ω' _
  congr 1
  unfold weightedInner
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro xs _
  simp [Finset.prod_mul_distrib, mul_assoc]

theorem tensorNormSquared_nonneg (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ν : β → ℝ) (φ : β → α → ℝ) (k : ℕ) :
    0 ≤ tensorNormSquared w ν φ k := by
  apply Finset.sum_nonneg
  intro xs _
  exact mul_nonneg (Finset.prod_nonneg fun i _ => hw (xs i)) (sq_nonneg _)

/-- The zero-order chaos vanishes because a difference of priors has mass zero. -/
theorem tensorNormSquared_zero (w : α → ℝ) (ν : β → ℝ) (φ : β → α → ℝ)
    (hν : ∑ ω, ν ω = 0) : tensorNormSquared w ν φ 0 = 0 := by
  rw [tensorNormSquared_gram]
  simp [← Finset.mul_sum, hν]

/-- Exponential kernel expansion into nonnegative tensor norm coefficients.
This is the finite-space analytic identity used in the Poisson chaos proof. -/
theorem exponential_kernel_chaos_hasSum (w : α → ℝ) (ν : β → ℝ)
    (φ : β → α → ℝ) (c : ℝ) :
    HasSum (fun k => c ^ k / k.factorial * tensorNormSquared w ν φ k)
      (∑ ω, ∑ ω', ν ω * ν ω' * Real.exp (c * weightedInner w φ ω ω')) := by
  have hh : HasSum (fun k => ∑ ω, ∑ ω', ν ω * ν ω' *
      ((c * weightedInner w φ ω ω') ^ k / k.factorial))
      (∑ ω, ∑ ω', ν ω * ν ω' * Real.exp (c * weightedInner w φ ω ω')) := by
    apply hasSum_sum
    intro ω _
    apply hasSum_sum
    intro ω' _
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (c * weightedInner w φ ω ω')).mul_left
        (ν ω * ν ω')
  convert hh using 1
  ext k
  rw [tensorNormSquared_gram]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ω' _
  rw [mul_pow]
  ring

/-- Count-conditioned squared likelihood mixture for a finite marked space. -/
theorem poisson_likelihood_square_hasSum (P : FiniteLaw α) (ν : β → ℝ)
    (ψ : β → α → ℝ) (rate c : ℝ) :
    HasSum (fun n => poissonMass rate n * (c⁻¹) ^ n *
      tensorNormSquared P.mass ν ψ n)
      (∑ ω, ∑ ω', ν ω * ν ω' *
        Real.exp (rate * (c⁻¹ * weightedInner P.mass ψ ω ω' - 1))) := by
  have hh : HasSum (fun n => ∑ ω, ∑ ω', ν ω * ν ω' *
      (poissonMass rate n * (c⁻¹ * weightedInner P.mass ψ ω ω') ^ n))
      (∑ ω, ∑ ω', ν ω * ν ω' *
        Real.exp (rate * (c⁻¹ * weightedInner P.mass ψ ω ω' - 1))) := by
    apply hasSum_sum
    intro ω _
    apply hasSum_sum
    intro ω' _
    exact (poisson_generating_hasSum rate (c⁻¹ * weightedInner P.mass ψ ω ω')).mul_left
      (ν ω * ν ω')
  convert hh using 1
  ext n
  rw [tensorNormSquared_gram]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ω' _
  rw [mul_pow]
  ring

omit [Fintype β] in
theorem centered_likelihood_inner (P : FiniteLaw α) (φ : β → α → ℝ)
    (hφ : ∀ ω, ∑ x, P.mass x * φ ω x = 0) (ω ω' : β) :
    weightedInner P.mass (fun ω x => 1 + φ ω x) ω ω' =
      1 + weightedInner P.mass φ ω ω' := by
  unfold weightedInner
  have hx (x : α) : P.mass x * (1 + φ ω x) * (1 + φ ω' x) =
      P.mass x + P.mass x * φ ω x + P.mass x * φ ω' x +
        P.mass x * φ ω x * φ ω' x := by ring
  simp_rw [hx]
  simp [Finset.sum_add_distrib, P.total, hφ]

/-- Exact finite-marked-space counterpart of the weighted Poisson chaos identity.
`rate` is the total intensity and `P` is the mark law. The square on the left is
the likelihood difference conditional on the Poisson count. -/
theorem finite_poisson_chaos_identity (P : FiniteLaw α) (ν : β → ℝ)
    (φ : β → α → ℝ) (rate c : ℝ)
    (hφ : ∀ ω, ∑ x, P.mass x * φ ω x = 0) :
    (∑' n, poissonMass rate n * (c⁻¹) ^ n *
      tensorNormSquared P.mass ν (fun ω x => 1 + φ ω x) n) =
      Real.exp (rate * (c⁻¹ - 1)) *
        ∑' k, (rate * c⁻¹) ^ k / k.factorial * tensorNormSquared P.mass ν φ k := by
  rw [(poisson_likelihood_square_hasSum P ν (fun ω x => 1 + φ ω x) rate c).tsum_eq,
    (exponential_kernel_chaos_hasSum P.mass ν φ (rate * c⁻¹)).tsum_eq]
  simp_rw [centered_likelihood_inner P φ hφ]
  have he (ω ω' : β) :
      Real.exp (rate * (c⁻¹ * (1 + weightedInner P.mass φ ω ω') - 1)) =
        Real.exp (rate * (c⁻¹ - 1)) * Real.exp ((rate * c⁻¹) * weightedInner P.mass φ ω ω') := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ω' _
  ring

/-- Positive-order form of the chaos identity when the signed prior has mass zero. -/
theorem finite_poisson_chaos_identity_positive_orders (P : FiniteLaw α) (ν : β → ℝ)
    (φ : β → α → ℝ) (rate c : ℝ)
    (hφ : ∀ ω, ∑ x, P.mass x * φ ω x = 0) (hν : ∑ ω, ν ω = 0) :
    (∑' n, poissonMass rate n * (c⁻¹) ^ n *
      tensorNormSquared P.mass ν (fun ω x => 1 + φ ω x) n) =
      Real.exp (rate * (c⁻¹ - 1)) *
        ∑' k, (rate * c⁻¹) ^ (k + 1) / (k + 1).factorial *
          tensorNormSquared P.mass ν φ (k + 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (exponential_kernel_chaos_hasSum P.mass ν φ (rate * c⁻¹))
  simp only [Finset.sum_range_one, tensorNormSquared_zero P.mass ν φ hν,
    mul_zero, sub_zero] at h
  rw [h.tsum_eq]
  rw [finite_poisson_chaos_identity P ν φ rate c hφ,
    (exponential_kernel_chaos_hasSum P.mass ν φ (rate * c⁻¹)).tsum_eq]

end
end RoughRegime.Lower
