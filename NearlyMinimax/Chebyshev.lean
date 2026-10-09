module

public import NearlyMinimax.MomentRules
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Fin


@[expose] public section

noncomputable section

namespace NearlyMinimax

open Polynomial Finset

/-- The nonnegative real inverse hyperbolic cosine on `[1,∞)`. -/
def exteriorTau (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))

theorem cosh_exteriorTau (x : ℝ) (hx : 1 ≤ x) : Real.cosh (exteriorTau x) = x := by
  have hs : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hp : 0 < x + Real.sqrt (x ^ 2 - 1) := by positivity
  have hsq := Real.sq_sqrt hs
  have hinv : (x + Real.sqrt (x ^ 2 - 1))⁻¹ = x - Real.sqrt (x ^ 2 - 1) := by
    field_simp
    nlinarith
  rw [exteriorTau, Real.cosh_log hp, hinv]
  ring

theorem exteriorTau_nonneg (x : ℝ) (hx : 1 ≤ x) : 0 ≤ exteriorTau x := by
  apply Real.log_nonneg
  exact hx.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- The two forms of the paper's exterior exponent coincide. -/
theorem exteriorTau_sqrt_ratio (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    exteriorTau ((a + b) / (b - a)) =
      Real.log ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) := by
  have hb : 0 < b := ha.trans hab
  have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  have hsqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hslt : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  have hbap : 0 < b - a := sub_pos.mpr hab
  have hba : b - a ≠ 0 := by linarith
  have hsminus : Real.sqrt b - Real.sqrt a ≠ 0 := by linarith
  have hsplus : Real.sqrt b + Real.sqrt a ≠ 0 := by positivity
  have hroot : Real.sqrt (((a + b) / (b - a)) ^ 2 - 1) =
      2 * Real.sqrt a * Real.sqrt b / (b - a) := by
    have hr : 0 ≤ 2 * Real.sqrt a * Real.sqrt b / (b - a) := by positivity
    rw [← Real.sqrt_sq hr]
    congr 1
    rw [div_pow, div_pow, mul_pow, mul_pow, hsqa, hsqb]
    field_simp
    ring
  rw [exteriorTau, hroot]
  congr 1
  calc
    (a + b) / (b - a) + 2 * Real.sqrt a * Real.sqrt b / (b - a) =
      (Real.sqrt b + Real.sqrt a) ^ 2 /
        ((Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a)) := by
          rw [← add_div]
          congr 1 <;> nlinarith
    _ = (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) := by
      field_simp

/-- Exponential decay parameter corresponding to the paper's exponent. -/
theorem exp_neg_exteriorTau (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Real.exp (-exteriorTau ((a + b) / (b - a))) =
      (Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a) := by
  have hslt : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  have hd : 0 < Real.sqrt b - Real.sqrt a := sub_pos.mpr hslt
  have hratio : 0 < (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) := by
    have hb := ha.trans hab
    positivity
  rw [exteriorTau_sqrt_ratio a b ha hab, Real.exp_neg, Real.exp_log hratio, inv_div]

/-- A Chebyshev polynomial has degree at most its nonnegative index. -/
theorem chebyshev_natDegree_le (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      have he : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
      have he1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
      rw [he, Polynomial.Chebyshev.T_add_two]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · have h := Polynomial.natDegree_mul_le
          (p := (2 : ℝ[X]) * X) (q := Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1))
        have hd : ((2 : ℝ[X]) * X).natDegree ≤ 1 := by simp
        rw [← he1] at h ⊢
        omega
      · omega

/-- Reflection parity of the Chebyshev polynomials. -/
theorem chebyshev_eval_neg (n : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (-x) =
      (-1 : ℝ) ^ n * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      have he : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
      have he1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
      rw [he, Polynomial.Chebyshev.T_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X, ← he1, ih0, ih1]
      rw [pow_succ, pow_succ]
      ring

/-- The standard Chebyshev–Lobatto nodes, in decreasing order. -/
def lobattoNode (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  Real.cos ((i.val : ℝ) * Real.pi / n)

private theorem lobatto_angle_mem (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (i.val : ℝ) * Real.pi / n ∈ Set.Icc 0 Real.pi := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_iff₀ hnp).mpr
    have hi : (i.val : ℝ) ≤ n := by exact_mod_cast (show i.val ≤ n by omega)
    nlinarith [Real.pi_pos]

theorem lobattoNode_strictAnti (n : ℕ) (hn : 1 ≤ n) : StrictAnti (lobattoNode n) := by
  intro i j hij
  apply Real.strictAntiOn_cos (lobatto_angle_mem n hn i) (lobatto_angle_mem n hn j)
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hn : (0 : ℝ) < n)
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact_mod_cast hij

/-- The exterior nodes appearing in the finite moment rule. -/
def exteriorNode (a b : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (a + b) / 2 + ((b - a) / 2) * lobattoNode n i

theorem exteriorNode_strictAnti (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 1 ≤ n) :
    StrictAnti (exteriorNode a b n) := by
  intro i j hij
  dsimp [exteriorNode]
  have h := mul_lt_mul_of_pos_left (lobattoNode_strictAnti n hn hij)
    (by linarith : (0 : ℝ) < (b - a) / 2)
  linarith

theorem exteriorNode_mem (a b : ℝ) (hab : a ≤ b) (n : ℕ) (i : Fin (n + 1)) :
    exteriorNode a b n i ∈ Set.Icc a b := by
  dsimp [exteriorNode, lobattoNode]
  constructor <;> nlinarith [Real.cos_le_one ((i.val : ℝ) * Real.pi / n),
    Real.neg_one_le_cos ((i.val : ℝ) * Real.pi / n)]

/-- The explicit cardinal weights from the paper. -/
def exteriorWeight (a b : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
    exteriorNode a b n j / (exteriorNode a b n j - exteriorNode a b n i)

/-- Chebyshev–Lobatto exterior cardinal weights reproduce evaluation at zero through degree `n`. -/
theorem exterior_rule_exact (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 1 ≤ n)
    (P : ℝ[X]) (hP : P.degree ≤ n) :
    (∑ i : Fin (n + 1), exteriorWeight a b n i * P.eval (exteriorNode a b n i)) =
      P.eval 0 := by
  apply exterior_product_rule_exact Finset.univ (exteriorNode a b n)
    (exteriorNode_strictAnti a b hab n hn).injective.injOn
  simpa using hP.trans_lt (show (n : WithBot ℕ) < n + 1 by exact_mod_cast Nat.lt_succ_self n)

private theorem positive_decreasing_weight_sign (n : ℕ) (z : Fin (n + 1) → ℝ)
    (hz : ∀ i, 0 < z i) (hanti : StrictAnti z) (i : Fin (n + 1)) :
    (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, z j / (z j - z i)) =
      (-1 : ℝ) ^ (n - i.val) *
        |∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, z j / (z j - z i)| := by
  let S := (Finset.univ : Finset (Fin (n + 1))).erase i
  have hf (j : Fin (n + 1)) (hj : j ∈ S) :
      z j / (z j - z i) = (if i < j then (-1 : ℝ) else 1) * |z j / (z j - z i)| := by
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    by_cases hij : i < j
    · rw [if_pos hij, abs_of_neg (div_neg_of_pos_of_neg (hz j)
        (sub_neg.mpr (hanti hij)))]
      ring
    · have hji' : j < i := lt_of_le_of_ne (le_of_not_gt hij) hji
      rw [if_neg hij, abs_of_pos (div_pos (hz j) (sub_pos.mpr (hanti hji'))), one_mul]
  have hs : (∏ j ∈ S, if i < j then (-1 : ℝ) else 1) = (-1 : ℝ) ^ (n - i.val) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    have hset : S.filter (fun j => i < j) = Finset.Ioi i := by
      ext j
      simp [S, Finset.mem_Ioi]
      omega
    rw [hset, Fin.card_Ioi]
    congr 1
  change (∏ j ∈ S, z j / (z j - z i)) = _
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hf

/-- The Chebyshev polynomial rescaled to the interval `[a,b]`. -/
def intervalChebyshev (a b : ℝ) (n : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
    ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹))

theorem intervalChebyshev_degree (a b : ℝ) (n : ℕ) :
    (intervalChebyshev a b n).degree ≤ n := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_comp_le.trans
  have hd : ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹) : ℝ[X]).natDegree ≤ 1 := by
    apply Polynomial.natDegree_mul_le.trans
    simp
  exact (Nat.mul_le_mul (chebyshev_natDegree_le n) hd).trans (by simp)

theorem intervalChebyshev_at_node (a b : ℝ) (hab : a < b) (n : ℕ)
    (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (intervalChebyshev a b n).eval (exteriorNode a b n i) = (-1 : ℝ) ^ i.val := by
  have hR : (b - a) / 2 ≠ 0 := by linarith
  have hba : b - a ≠ 0 := by linarith
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnorm : (exteriorNode a b n i - (a + b) / 2) * ((b - a) / 2)⁻¹ =
      lobattoNode n i := by
    dsimp [exteriorNode]
    field_simp [hba]
    ring
  simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
  rw [lobattoNode, Polynomial.Chebyshev.T_real_cos]
  simp only [Int.cast_natCast]
  have hang : (n : ℝ) * ((i.val : ℝ) * Real.pi / n) = (i.val : ℝ) * Real.pi := by
    field_simp
  rw [hang]
  simpa using Real.cos_nat_mul_pi_sub 0 i.val

/-- The exterior weight signs alternate along the Lobatto nodes. -/
theorem exterior_weight_sign (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ)
    (hn : 1 ≤ n) (i : Fin (n + 1)) :
    exteriorWeight a b n i = (-1 : ℝ) ^ (n - i.val) * |exteriorWeight a b n i| := by
  apply positive_decreasing_weight_sign
  · intro j
    exact ha.trans_le (exteriorNode_mem a b (le_of_lt hab) n j).1
  · exact exteriorNode_strictAnti a b hab n hn

/-- The exact atom variation of the exterior finite rule, expressed through inverse cosh. -/
theorem exterior_rule_variation (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ)
    (hn : 1 ≤ n) :
    (∑ i : Fin (n + 1), |exteriorWeight a b n i|) =
      Real.cosh ((n : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have hba : b - a ≠ 0 := by linarith
  have hR : (b - a) / 2 ≠ 0 := by linarith
  have hratio : 1 ≤ (a + b) / (b - a) := by
    apply (le_div_iff₀ (by linarith : 0 < b - a)).mpr
    linarith
  have hnorm : (0 - (a + b) / 2) * ((b - a) / 2)⁻¹ = -((a + b) / (b - a)) := by
    field_simp
    ring
  have heval : (intervalChebyshev a b n).eval 0 =
      (-1 : ℝ) ^ n * Real.cosh ((n : ℝ) * exteriorTau ((a + b) / (b - a))) := by
    simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
    rw [chebyshev_eval_neg]
    congr 1
    calc
      _ = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (Real.cosh (exteriorTau ((a + b) / (b - a)))) := by
          rw [cosh_exteriorTau _ hratio]
      _ = _ := by
        rw [Polynomial.Chebyshev.T_real_cosh]
        simp
  have hexact := exterior_rule_exact a b hab n hn (intervalChebyshev a b n)
    (intervalChebyshev_degree a b n)
  have hnode : ∀ i : Fin (n + 1), exteriorWeight a b n i *
      (intervalChebyshev a b n).eval (exteriorNode a b n i) =
        (-1 : ℝ) ^ n * |exteriorWeight a b n i| := by
    intro i
    rw [intervalChebyshev_at_node a b hab n hn i]
    nth_rw 1 [exterior_weight_sign a b ha hab n hn i]
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (by omega : i.val ≤ n)]
  simp_rw [hnode] at hexact
  rw [← Finset.mul_sum, heval] at hexact
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) hexact

/-- The exterior rule's variation has the exponential bound used in local packet costs. -/
theorem exterior_rule_variation_le_exp (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ i : Fin (n + 1), |exteriorWeight a b n i|) ≤
      Real.exp ((n : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [exterior_rule_variation a b ha hab n hn, Real.cosh_eq]
  have hratio : 1 ≤ (a + b) / (b - a) := by
    apply (le_div_iff₀ (by linarith : 0 < b - a)).mpr
    linarith
  have ht : 0 ≤ (n : ℝ) * exteriorTau ((a + b) / (b - a)) := by
    exact mul_nonneg (Nat.cast_nonneg n) (exteriorTau_nonneg _ hratio)
  have he := Real.exp_le_exp.mpr (show
      -((n : ℝ) * exteriorTau ((a + b) / (b - a))) ≤
      (n : ℝ) * exteriorTau ((a + b) / (b - a)) by linarith)
  linarith

/-- The exterior rule has evaluation-at-zero monomial moments. -/
theorem exterior_rule_moments (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : k ≤ n) :
    (∑ i : Fin (n + 1), exteriorWeight a b n i * exteriorNode a b n i ^ k) =
      if k = 0 then 1 else 0 := by
  have hd : (X ^ k : ℝ[X]).degree ≤ n := by
    simpa only [degree_X_pow, Nat.cast_withBot] using WithBot.coe_le_coe.mpr hk
  by_cases hk0 : k = 0
  · subst k
    simpa using exterior_rule_exact a b hab n hn (X ^ 0) hd
  · simpa [zero_pow hk0, hk0] using exterior_rule_exact a b hab n hn (X ^ k) hd

/-- The finite rule controls exterior evaluation of every polynomial of its degree range. -/
theorem exterior_polynomial_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (n : ℕ) (hn : 1 ≤ n) (P : ℝ[X]) (hP : P.degree ≤ n) (B : ℝ)
    (hB : ∀ i : Fin (n + 1), |P.eval (exteriorNode a b n i)| ≤ B) :
    |P.eval 0| ≤ Real.cosh ((n : ℝ) * exteriorTau ((a + b) / (b - a))) * B := by
  rw [← exterior_rule_exact a b hab n hn P hP]
  calc
    |∑ i : Fin (n + 1), exteriorWeight a b n i * P.eval (exteriorNode a b n i)| ≤
        ∑ i : Fin (n + 1), |exteriorWeight a b n i * P.eval (exteriorNode a b n i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n + 1), |exteriorWeight a b n i| * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, exterior_rule_variation a b ha hab n hn]

end NearlyMinimax
