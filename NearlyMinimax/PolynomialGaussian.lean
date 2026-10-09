module

public import NearlyMinimax.Allocation
public import NearlyMinimax.GaussianSum


@[expose] public section

/-!
# Polynomial absorption and the abstract finite bias allocation

These are deterministic analytic lemmas for the `U12` bias allocation. The
polynomial factor is absorbed using a proved term of the exponential series.
The final finite-sum bound assumes the scalar allocation identities and their
budget reserve, rather than assuming any estimator or minimax risk bound.
-/

noncomputable section
open scoped BigOperators

namespace NearlyMinimax

/-- An explicit constant that absorbs any fixed polynomial into half the exponential. -/
def polynomialGaussianConstant (r : ℕ) (a : ℝ) : ℝ :=
  (r.factorial : ℝ) / (a / 2) ^ r * Real.exp (a / 2)

theorem polynomialGaussianConstant_pos (r : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < polynomialGaussianConstant r a := by
  unfold polynomialGaussianConstant
  positivity

/-- The exponential-series argument behind the polynomial Gaussian absorption. -/
theorem polynomial_exp_absorption (r : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (1 + t) ^ r * Real.exp (-a * t) ≤
      polynomialGaussianConstant r a * Real.exp (-(a / 2) * t) := by
  have hδ : 0 < a / 2 := by positivity
  have hf : 0 < (r.factorial : ℝ) := by positivity
  have hh := Real.pow_div_factorial_le_exp (a / 2 * (1 + t))
    (by positivity : 0 ≤ a / 2 * (1 + t)) r
  have hp : (1 + t) ^ r ≤
      (r.factorial : ℝ) / (a / 2) ^ r * Real.exp (a / 2 * (1 + t)) := by
    have hb := (div_le_iff₀ hf).1 hh
    rw [mul_pow] at hb
    calc
      (1 + t) ^ r ≤ (Real.exp (a / 2 * (1 + t)) * (r.factorial : ℝ)) / (a / 2) ^ r := by
        apply (le_div_iff₀ (pow_pos hδ r)).2
        simpa [mul_comm] using hb
      _ = (r.factorial : ℝ) / (a / 2) ^ r * Real.exp (a / 2 * (1 + t)) := by ring
  have hs := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-a * t)).le
  apply hs.trans_eq
  unfold polynomialGaussianConstant
  have he : Real.exp (a / 2 * (1 + t)) * Real.exp (-a * t) =
      Real.exp (a / 2) * Real.exp (-(a / 2) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    ((r.factorial : ℝ) / (a / 2) ^ r * Real.exp (a / 2 * (1 + t))) * Real.exp (-a * t) =
        (r.factorial : ℝ) / (a / 2) ^ r *
          (Real.exp (a / 2 * (1 + t)) * Real.exp (-a * t)) := by ring
    _ = _ := by rw [he]; ring

/-- The exact polynomial absorption step at the paper's rescaled Gaussian variable. -/
theorem polynomial_gaussian_absorption (r : ℕ) {a S u : ℝ}
    (ha : 0 < a) (hS : 0 < S) :
    (1 + u ^ 2 / S) ^ r * Real.exp (-a * u ^ 2 / S) ≤
      polynomialGaussianConstant r a * Real.exp (-(a / 2) * u ^ 2 / S) := by
  have h := polynomial_exp_absorption r ha (div_nonneg (sq_nonneg u) hS.le)
  have h₁ : -a * (u ^ 2 / S) = -a * u ^ 2 / S := by ring
  have h₂ : -(a / 2) * (u ^ 2 / S) = -(a / 2) * u ^ 2 / S := by ring
  rwa [h₁, h₂] at h

/-- Floor and coordinate subtraction give both needed bounds on approximation degree. -/
theorem profile_approximation_degree_bounds {β Q : ℝ} (q : ℕ)
    (hβQ : 0 ≤ β * Q) (hq : q ≤ Nat.floor (β * Q)) :
    β * Q - (q : ℝ) - 1 ≤ ((Nat.floor (β * Q) - q : ℕ) : ℝ) ∧
      ((Nat.floor (β * Q) - q : ℕ) : ℝ) + 1 ≤ β * Q + 1 := by
  have hf := Nat.floor_le hβQ
  have hl := Nat.lt_floor_add_one (β * Q)
  rw [Nat.cast_sub hq]
  constructor <;> linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))]

/-- The profile upper bound controls the entire fixed polynomial prefactor. -/
theorem profile_polynomial_prefactor_bound (r : ℕ) {β S z m : ℝ}
    (hβ : 0 ≤ β) (hS : 1 ≤ S) (hm : 0 ≤ m + 1)
    (hmQ : m + 1 ≤ β * quadraticProfile S z + 1) :
    (m + 1) ^ r ≤ (1 + 3 * β / 2) ^ r * S ^ r *
      (1 + (z - S / 2) ^ 2 / S) ^ r := by
  have hS₀ : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hQ := quadraticProfile_gaussian_upper (z := z) hS₀
  have ht : 0 ≤ (z - S / 2) ^ 2 / S := div_nonneg (sq_nonneg _) hS₀.le
  have hupper : m + 1 ≤ (1 + 3 * β / 2) * S *
      (1 + (z - S / 2) ^ 2 / S) := by
    rw [show 3 * (z - S / 2) ^ 2 / (2 * S) =
      3 / 2 * ((z - S / 2) ^ 2 / S) by ring] at hQ
    have hb := mul_le_mul_of_nonneg_left hQ hβ
    have htriple := mul_nonneg hβ (mul_nonneg (sub_nonneg.mpr hS) ht)
    nlinarith [mul_nonneg hS₀.le ht, mul_nonneg hβ hS₀.le]
  have hp := pow_le_pow_left₀ hm hupper r
  simpa only [mul_pow, mul_assoc] using hp

/-- The logarithmic reserve cancels `S^r` leaving the Gaussian normalizer. -/
theorem pow_mul_log_factor_eq_inv_sqrt (r : ℕ) {S : ℝ} (hS : 0 < S) :
    S ^ r * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S) = 1 / Real.sqrt S := by
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  rw [← Real.exp_log (pow_pos hS r), Real.log_pow, ← Real.exp_add]
  simp only [one_div]
  rw [← Real.exp_log hsqrt, ← Real.exp_neg]
  congr 1
  rw [Real.log_sqrt hS.le]
  ring

/-- Explicit constant for the normalized term bound in `eq:U12-term`. -/
def allocationBiasTermConstant (r q : ℕ) (β θ τ : ℝ) : ℝ :=
  (1 + 3 * β / 2) ^ r * Real.exp (τ * ((q : ℝ) + 1)) * polynomialGaussianConstant r θ

theorem allocationBiasTermConstant_pos (r q : ℕ) {β θ τ : ℝ}
    (hβ : 0 ≤ β) (hθ : 0 < θ) : 0 < allocationBiasTermConstant r q β θ τ := by
  unfold allocationBiasTermConstant
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _))
    (polynomialGaussianConstant_pos r hθ)

/-- The profile identity and degree lower bound produce the Gaussian decay. -/
theorem allocation_bias_mass_bound (r q : ℕ) {β θ τ S z ell T m : ℝ}
    (_hθ : 0 < θ) (hτ : 0 < τ) (hS : 0 < S) (hθβ : τ * β = θ)
    (hm : β * quadraticProfile S z - (q : ℝ) - 1 ≤ m)
    (hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T)) :
    Real.exp (-θ * (z - ell - T) - τ * m) ≤
      Real.exp (τ * ((q : ℝ) + 1)) *
        Real.exp (-((r : ℝ) + 1 / 2) * Real.log S) *
          Real.exp (-θ * (z - S / 2) ^ 2 / S) := by
  have hml := mul_le_mul_of_nonneg_left hm hτ.le
  have hrewrite : τ * (β * quadraticProfile S z - (q : ℝ) - 1) =
      θ * quadraticProfile S z - τ * ((q : ℝ) + 1) := by
    rw [← hθβ]
    ring
  rw [hrewrite] at hml
  have hid : θ * (z + quadraticProfile S z - S) = θ * (z - S / 2) ^ 2 / S := by
    rw [quadraticProfile_bias_identity hS.ne']
    ring
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  ring_nf at hml hreserve hid ⊢
  linarith

/-- The actual deterministic bias summand is bounded by a normalized Gaussian. -/
theorem allocation_bias_term_bound (r q : ℕ) {β θ τ S z ell T m : ℝ}
    (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ) (hmpos : 0 ≤ m + 1)
    (hml : β * quadraticProfile S z - (q : ℝ) - 1 ≤ m)
    (hmu : m + 1 ≤ β * quadraticProfile S z + 1)
    (hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T)) :
    Real.exp (-θ * (z - ell - T) - τ * m) * (m + 1) ^ r ≤
      allocationBiasTermConstant r q β θ τ / Real.sqrt S *
        Real.exp (-(θ / 2) * (z - S / 2) ^ 2 / S) := by
  have hS₀ : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hm := allocation_bias_mass_bound r q hθ hτ hS₀ hθβ hml hreserve
  have hp := profile_polynomial_prefactor_bound r hβ hS hmpos hmu
  have ha := polynomial_gaussian_absorption r hθ (u := z - S / 2) hS₀
  have hc : 0 ≤ (1 + 3 * β / 2) ^ r * Real.exp (τ * ((q : ℝ) + 1)) := by positivity
  have hb : 0 ≤ S ^ r * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S) := by positivity
  calc
    _ ≤ (Real.exp (τ * ((q : ℝ) + 1)) *
        Real.exp (-((r : ℝ) + 1 / 2) * Real.log S) *
          Real.exp (-θ * (z - S / 2) ^ 2 / S)) *
            ((1 + 3 * β / 2) ^ r * S ^ r * (1 + (z - S / 2) ^ 2 / S) ^ r) :=
      mul_le_mul hm hp (pow_nonneg hmpos r) (by positivity)
    _ = ((1 + 3 * β / 2) ^ r * Real.exp (τ * ((q : ℝ) + 1))) *
        (S ^ r * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S)) *
          ((1 + (z - S / 2) ^ 2 / S) ^ r * Real.exp (-θ * (z - S / 2) ^ 2 / S)) := by ring
    _ ≤ ((1 + 3 * β / 2) ^ r * Real.exp (τ * ((q : ℝ) + 1))) *
        (S ^ r * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S)) *
          (polynomialGaussianConstant r θ * Real.exp (-(θ / 2) * (z - S / 2) ^ 2 / S)) :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg hc hb)
    _ = _ := by
      rw [pow_mul_log_factor_eq_inv_sqrt r hS₀]
      unfold allocationBiasTermConstant
      ring

/-- The full finite scalar bias sum, under the quadratic profile and budget conditions. -/
theorem finite_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    (u₀ b β θ τ S ell T : ℝ) (m : ℕ → ℕ)
    (hb : 0 < b) (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ)
    (hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T))
    (hml : ∀ j ∈ A, β * quadraticProfile S (u₀ + (j : ℝ) * b + S / 2) - (q : ℝ) - 1 ≤ (m j : ℝ))
    (hmu : ∀ j ∈ A, (m j : ℝ) + 1 ≤ β * quadraticProfile S (u₀ + (j : ℝ) * b + S / 2) + 1) :
    (∑ j ∈ A, Real.exp (-θ * (u₀ + (j : ℝ) * b + S / 2 - ell - T) - τ * (m j : ℝ)) *
      ((m j : ℝ) + 1) ^ r) ≤
        allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b) := by
  have hterm j (hj : j ∈ A) := allocation_bias_term_bound r q hβ hθ hτ hS hθβ
    (by positivity : 0 ≤ (m j : ℝ) + 1) (hml j hj) (hmu j hj) hreserve
  have hsum : (∑ j ∈ A, Real.exp (-θ * (u₀ + (j : ℝ) * b + S / 2 - ell - T) - τ * (m j : ℝ)) *
      ((m j : ℝ) + 1) ^ r) ≤
        ∑ j ∈ A, allocationBiasTermConstant r q β θ τ / Real.sqrt S *
          Real.exp (-(θ / 2) * (u₀ + (j : ℝ) * b) ^ 2 / S) := by
    apply Finset.sum_le_sum
    intro j hj
    simpa only [add_sub_cancel_right] using hterm j hj
  apply hsum.trans
  rw [← Finset.mul_sum]
  have hgauss := GaussianSum.normalized_gaussian_lattice_sum_le A u₀ (θ / 2) b S
    (by positivity) hb hS
  have hc := (allocationBiasTermConstant_pos r q hβ hθ (τ := τ)).le
  have hh := mul_le_mul_of_nonneg_left hgauss hc
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using hh

/-- The resulting finite-sum constant, independent of center and number of levels. -/
def allocationBiasSumConstant (r q : ℕ) (β θ τ b : ℝ) : ℝ :=
  allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b)

theorem allocationBiasSumConstant_pos (r q : ℕ) {β θ τ b : ℝ}
    (hβ : 0 ≤ β) (hθ : 0 < θ) (hb : 0 < b) :
    0 < allocationBiasSumConstant r q β θ τ b := by
  unfold allocationBiasSumConstant
  exact mul_pos (allocationBiasTermConstant_pos r q hβ hθ) (by positivity)

/-- A single scalar threshold supplies all coordinate-order guards in the finite sum. -/
theorem profile_coordinate_order_admissible (q : ℕ) {β S z : ℝ}
    (hβ : 0 ≤ β) (hS : 0 < S) (hthreshold : (q : ℝ) ≤ β * S / 4) :
    q ≤ Nat.floor (β * quadraticProfile S z) := by
  apply Nat.le_floor
  have hQ := mul_le_mul_of_nonneg_left (quadraticProfile_lower (z := z) hS) hβ
  linarith

/-- The finite bias sum in the original cell-mass variables, assuming their log identities. -/
theorem raw_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    (u₀ b β θ τ S ell T Kstar : ℝ) (K : ℕ → ℝ) (m : ℕ → ℕ)
    (hb : 0 < b) (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ) (hKstar : 0 < Kstar)
    (hK : ∀ j ∈ A, 0 < K j)
    (hlog : ∀ j ∈ A, Real.log (K j) - Real.log Kstar =
      u₀ + (j : ℝ) * b + S / 2 - ell - T)
    (hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T))
    (hml : ∀ j ∈ A, β * quadraticProfile S (u₀ + (j : ℝ) * b + S / 2) - (q : ℝ) - 1 ≤ (m j : ℝ))
    (hmu : ∀ j ∈ A, (m j : ℝ) + 1 ≤ β * quadraticProfile S (u₀ + (j : ℝ) * b + S / 2) + 1) :
    (∑ j ∈ A, (K j) ^ (-θ) * ((m j : ℝ) + 1) ^ r * (Real.exp (-τ)) ^ (m j)) ≤
      allocationBiasSumConstant r q β θ τ b * Kstar ^ (-θ) := by
  have he (j : ℕ) (hj : j ∈ A) : (K j) ^ (-θ) * (Real.exp (-τ)) ^ (m j) =
      Kstar ^ (-θ) * Real.exp (-θ * (u₀ + (j : ℝ) * b + S / 2 - ell - T) - τ * (m j : ℝ)) := by
    rw [Real.rpow_def_of_pos (hK j hj), Real.rpow_def_of_pos hKstar,
      ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have hlogeq : Real.log (K j) = Real.log Kstar +
        (u₀ + (j : ℝ) * b + S / 2 - ell - T) := by linarith [hlog j hj]
    rw [hlogeq]
    ring
  have hsum := finite_allocation_bias_sum_bound A r q u₀ b β θ τ S ell T m
    hb hβ hθ hτ hS hθβ hreserve hml hmu
  calc
    _ = ∑ j ∈ A, Kstar ^ (-θ) *
        (Real.exp (-θ * (u₀ + (j : ℝ) * b + S / 2 - ell - T) - τ * (m j : ℝ)) * ((m j : ℝ) + 1) ^ r) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ((K j) ^ (-θ) * (Real.exp (-τ)) ^ (m j)) * ((m j : ℝ) + 1) ^ r := by ring
        _ = _ := by rw [he j hj]; ring
    _ = Kstar ^ (-θ) * ∑ j ∈ A,
        Real.exp (-θ * (u₀ + (j : ℝ) * b + S / 2 - ell - T) - τ * (m j : ℝ)) * ((m j : ℝ) + 1) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ Kstar ^ (-θ) *
        (allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_pos_of_pos hKstar _).le
    _ = _ := by unfold allocationBiasSumConstant; ring

/-- The actual floored approximation degree in the scalar allocation. -/
def allocatedApproximationDegree (β S z : ℝ) (q : ℕ) : ℕ :=
  Nat.floor (β * quadraticProfile S z) - q

/-- `eq:U12-sum` for the floored scalar allocation, under its explicit reserve and log-cell identities.
No summand or sum bound is an assumption of this theorem. -/
theorem floored_raw_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    (u₀ b β θ τ S ell T Kstar : ℝ) (K : ℕ → ℝ)
    (hb : 0 < b) (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ) (hKstar : 0 < Kstar)
    (hK : ∀ j ∈ A, 0 < K j)
    (hlog : ∀ j ∈ A, Real.log (K j) - Real.log Kstar =
      u₀ + (j : ℝ) * b + S / 2 - ell - T)
    (hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T))
    (hq : ∀ j ∈ A, q ≤ Nat.floor (β * quadraticProfile S (u₀ + (j : ℝ) * b + S / 2))) :
    (∑ j ∈ A, (K j) ^ (-θ) *
      ((allocatedApproximationDegree β S (u₀ + (j : ℝ) * b + S / 2) q : ℝ) + 1) ^ r *
        (Real.exp (-τ)) ^ (allocatedApproximationDegree β S (u₀ + (j : ℝ) * b + S / 2) q)) ≤
      allocationBiasSumConstant r q β θ τ b * Kstar ^ (-θ) := by
  have hS₀ : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hbounds j (hj : j ∈ A) := profile_approximation_degree_bounds q
    (mul_nonneg hβ ((by positivity : (0 : ℝ) ≤ S / 4).trans (quadraticProfile_lower hS₀))) (hq j hj)
  exact raw_allocation_bias_sum_bound A r q u₀ b β θ τ S ell T Kstar K
    (fun j => allocatedApproximationDegree β S (u₀ + (j : ℝ) * b + S / 2) q)
    hb hβ hθ hτ hS hθβ hKstar hK hlog hreserve
    (fun j hj => (hbounds j hj).1) (fun j hj => (hbounds j hj).2)

end NearlyMinimax
