module

public import Mathlib


@[expose] public section

/-!
# Finite factorial-series bounds for the upper allocation

The coefficients in the variance allocation are bounded directly. The finite
series is not replaced by an assumed variance bound. These scalar lemmas supply
the coarse and fine estimates in `upper_E.tex`, `eq:U13-wj` and `eq:U13-fine`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace NearlyMinimax

/-- The variance factorial series, summing `k! x^k` for `1 ≤ k ≤ D`. -/
def factorialSeries (D : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D, ((k + 1).factorial : ℝ) * x ^ (k + 1)

theorem factorialSeries_nonneg (D : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ factorialSeries D x := by
  unfold factorialSeries
  exact Finset.sum_nonneg fun k hk => by positivity

/-- The successive-term ratio is bounded by `1/2` throughout the finite sum. -/
theorem factorial_term_le_geometric {D k : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hD : (D : ℝ) * x ≤ 1 / 2) (hk : k < D) :
    ((k + 1).factorial : ℝ) * x ^ (k + 1) ≤ x * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkp : k < D := by omega
    have hratio : ((k + 2 : ℕ) : ℝ) * x ≤ 1 / 2 := by
      have hcast : ((k + 2 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ D)
      exact (mul_le_mul_of_nonneg_right hcast hx).trans hD
    have hprev := ih hkp
    calc
      (((k + 1 + 1).factorial : ℕ) : ℝ) * x ^ (k + 1 + 1) =
          (((k + 2 : ℕ) : ℝ) * x) * (((k + 1).factorial : ℝ) * x ^ (k + 1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
        push_cast
        ring
      _ ≤ (1 / 2 : ℝ) * (x * (1 / 2 : ℝ) ^ k) :=
        mul_le_mul hratio hprev (by positivity) (by norm_num)
      _ = x * (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-- The uniform coarse-level estimate in the paper. -/
theorem factorialSeries_coarse_bound {D : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hD : (D : ℝ) * x ≤ 1 / 2) :
    factorialSeries D x ≤ 2 * x := by
  have hg : (∑ k ∈ Finset.range D, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := D)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    convert h using 1 <;> norm_num
  unfold factorialSeries
  calc
    _ ≤ ∑ k ∈ Finset.range D, x * (1 / 2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact factorial_term_le_geometric hx hD (Finset.mem_range.1 hk)
    _ = x * ∑ k ∈ Finset.range D, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ x * 2 := mul_le_mul_of_nonneg_left hg hx
    _ = 2 * x := mul_comm _ _

/-- Factorials are bounded by the maximal degree to the corresponding power. -/
theorem factorial_cast_le_degree_pow {D k : ℕ} (hk : k ≤ D) :
    (k.factorial : ℝ) ≤ (D : ℝ) ^ k := by
  have h : k.factorial ≤ D ^ k :=
    (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hk k)
  exact_mod_cast h

/-- The finite fine-level estimate, prior to replacing `D` by its real upper bound. -/
theorem factorialSeries_fine_bound {D : ℕ} {x z B A : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hDx : (D : ℝ) * x ≤ Real.exp z)
    (hDz : (D : ℝ) * z ≤ B) (hDA : (D : ℝ) ≤ A) :
    factorialSeries D x ≤ A * Real.exp B := by
  unfold factorialSeries
  calc
    _ ≤ ∑ k ∈ Finset.range D, Real.exp B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkD : k + 1 ≤ D := Finset.mem_range.1 hk
      have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg D) hx) hDx (k + 1)
      have hcast : ((k + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hkD
      calc
        ((k + 1).factorial : ℝ) * x ^ (k + 1) ≤
            (D : ℝ) ^ (k + 1) * x ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (factorial_cast_le_degree_pow hkD) (by positivity)
        _ = ((D : ℝ) * x) ^ (k + 1) := by rw [mul_pow]
        _ ≤ (Real.exp z) ^ (k + 1) := hpow
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * z) := (Real.exp_nat_mul z (k + 1)).symm
        _ ≤ Real.exp B := Real.exp_le_exp.2
          ((mul_le_mul_of_nonneg_right hcast hz).trans hDz)
    _ = (D : ℝ) * Real.exp B := by simp
    _ ≤ A * Real.exp B := mul_le_mul_of_nonneg_right hDA (Real.exp_pos B).le

/-- Direct substitution of the fine-level allocation's `x = exp z/(C_D S)`. -/
theorem factorialSeries_fine_allocation {D : ℕ} {z β C_D S : ℝ}
    (hz : 0 ≤ z) (hCS : 0 < C_D * S)
    (hD : (D : ℝ) ≤ C_D * S) (hDz : (D : ℝ) * z ≤ β * S ^ 2 / 4) :
    factorialSeries D (Real.exp z / (C_D * S)) ≤
      C_D * S * Real.exp (β * S ^ 2 / 4) := by
  apply factorialSeries_fine_bound (div_nonneg (Real.exp_pos z).le hCS.le) hz _ hDz hD
  have hd := mul_le_mul_of_nonneg_right hD (div_nonneg (Real.exp_pos z).le hCS.le)
  have he : (C_D * S) * (Real.exp z / (C_D * S)) = Real.exp z := by
    rw [← mul_div_assoc, mul_comm (C_D * S), mul_div_cancel_right₀ _ hCS.ne']
  rwa [he] at hd

/-- Coarse weighting by `max{1,n/K}` cancels the sampling fraction exactly. -/
theorem factorialSeries_coarse_weighted {D : ℕ} {C₀ K n : ℝ}
    (hC : 0 ≤ C₀) (hK : 0 < K) (hn : 0 < n) (hKn : K ≤ n)
    (hD : (D : ℝ) * (C₀ * K / n) ≤ 1 / 2) :
    factorialSeries D (C₀ * K / n) * max 1 (n / K) ≤ 2 * C₀ := by
  have hm : 1 ≤ n / K := (le_div_iff₀ hK).2 (by simpa using hKn)
  rw [max_eq_right hm]
  have hseries := factorialSeries_coarse_bound (div_nonneg (mul_nonneg hC hK.le) hn.le) hD
  calc
    _ ≤ (2 * (C₀ * K / n)) * (n / K) :=
      mul_le_mul_of_nonneg_right hseries (div_nonneg hn.le hK.le)
    _ = 2 * C₀ := by field_simp

/-- The fine-level series remains bounded after its sampling weight. -/
theorem factorialSeries_fine_weighted {D : ℕ} {z β C₀ C_D S M : ℝ}
    (hz : 0 ≤ z) (_hC : 0 ≤ C₀) (hCS : 0 < C_D * S)
    (hD : (D : ℝ) ≤ C_D * S) (hDz : (D : ℝ) * z ≤ β * S ^ 2 / 4)
    (hM : 0 ≤ M) (hMb : M ≤ C₀ * C_D * S) :
    factorialSeries D (Real.exp z / (C_D * S)) * M ≤
      C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  have hs := factorialSeries_fine_allocation hz hCS hD hDz
  have h := mul_le_mul hs hMb hM (mul_nonneg hCS.le (Real.exp_pos _).le)
  apply h.trans_eq
  ring

/-- Flooring a nonnegative profile preserves its pointwise upper bound. -/
theorem floored_degree_upper {β Q : ℝ} (hβ : 0 ≤ β) (hQ : 0 ≤ Q) :
    (Nat.floor (β * Q) : ℝ) ≤ β * Q := Nat.floor_le (mul_nonneg hβ hQ)

/-- The degree-floor loss is less than one in the lower profile bound. -/
theorem floored_degree_lower {β S Q : ℝ} (hβ : 0 ≤ β) (hQ : S / 4 ≤ Q) :
    β * S / 4 - 1 < (Nat.floor (β * Q) : ℝ) := by
  have hm := mul_le_mul_of_nonneg_left hQ hβ
  have hf := Nat.lt_floor_add_one (β * Q)
  linarith

/-- A deterministic threshold ensuring enough degree for all feature coordinates. -/
theorem floored_degree_above_order {β S Q : ℝ} (q : ℕ)
    (hβ : 0 ≤ β) (hQ : S / 4 ≤ Q) (hS : (q : ℝ) + 2 ≤ β * S / 4) :
    q + 1 ≤ Nat.floor (β * Q) := by
  have hl := floored_degree_lower hβ hQ
  have hc : ((q + 1 : ℕ) : ℝ) ≤ (Nat.floor (β * Q) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hc

/-- The fixed subtraction in `eq:Udef-S` leaves the quadratic budget reserve. -/
theorem quadratic_allocation_budget {β H t S : ℝ}
    (hβ : 0 < β) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hdef : S = t - (1 + 2 * H / β)) :
    β * S ^ 2 / 4 + H * S ≤ β * t ^ 2 / 4 := by
  have ht : t = S + (1 + 2 * H / β) := by linarith
  have hid : β * t ^ 2 / 4 - (β * S ^ 2 / 4 + H * S) =
      β * (1 + 2 * H / β) ^ 2 / 4 + β * S / 2 := by
    rw [ht]
    field_simp
    ring
  have hn : 0 ≤ β * (1 + 2 * H / β) ^ 2 / 4 + β * S / 2 := by positivity
  linarith

/-- The budget directly supplies the spatial reserve in `eq:U13-reserve`. -/
theorem allocation_budget_reserve {β S η varpi L T : ℝ}
    (hbudget : β * S ^ 2 / 4 + (η + 2) * S ≤ 2 * varpi * L)
    (hη : 0 ≤ η) (hT : T ≤ S) :
    Real.exp (-2 * varpi * L + η * T) ≤ Real.exp (-β * S ^ 2 / 4 - 2 * S) := by
  apply Real.exp_le_exp.2
  have hm := mul_le_mul_of_nonneg_left hT hη
  linarith

/-- Combining the spatial reserve with the fine-level variance bound cancels the saddle cost. -/
theorem allocation_reserve_cancellation {reserve H A B S : ℝ}
    (_hreserve : 0 ≤ reserve) (hH : 0 ≤ H)
    (hr : reserve ≤ Real.exp (-B - 2 * S)) (hh : H ≤ A * Real.exp B) :
    reserve * H ≤ A * Real.exp (-2 * S) := by
  have h := mul_le_mul hr hh hH (Real.exp_pos _).le
  apply h.trans_eq
  calc
    Real.exp (-B - 2 * S) * (A * Real.exp B) =
        A * (Real.exp (-B - 2 * S) * Real.exp B) := by ring
    _ = A * Real.exp (-2 * S) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- The explicit residual variance upper bound tends to zero. -/
theorem tendsto_allocation_reserve_bound (C₀ C_D : ℝ) :
    Tendsto (fun S : ℝ => 2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (-2 * S))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) 2 (by norm_num)).const_mul
    (2 * C₀ * C_D ^ 2)
  convert h using 1 <;> simp [mul_assoc]

/-- In particular, the explicit fine-level bound is eventually at most one. -/
theorem eventually_allocation_reserve_bound_le_one (C₀ C_D : ℝ) :
    ∀ᶠ S : ℝ in atTop,
      2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (-2 * S) ≤ 1 :=
  ((tendsto_allocation_reserve_bound C₀ C_D).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun S h => h.le

end NearlyMinimax
