module

public import NearlyMinimax.Model
public import NearlyMinimax.Ternary


@[expose] public section

/-! Numeric constants for the interior zero-regression ternary submodel.
All constants are constructed from the strict margins in `ModelConstants`.
No statistical risk or testing conclusion is assumed here. -/

noncomputable section

namespace NearlyMinimax

open Set

/-- Uniform numerical guards for the one-dimensional ternary variance path. -/
structure ParametricTernaryConstants {d : ℕ} (C : ModelConstants d) where
  a : ℝ
  l : ℝ
  r : ℝ
  cf : ℝ
  Cf : ℝ
  delta : ℝ
  a_pos : 0 < a
  l_pos : 0 < l
  lower_le : C.varianceLower ≤ l
  interval : l < r
  upper_le : r ≤ C.varianceUpper
  variance_lt_square : r < a ^ 2
  fourth_le : a ^ 2 * r ≤ C.fourthBound
  cf_pos : 0 < cf
  Cf_pos : 0 < Cf
  mass_lower : ∀ V ∈ Icc l r, ∀ y : Fin 3, cf ≤ ternaryMass a 0 V y
  derivative_bound : ∀ y : Fin 3, |3 * ternaryVarianceDerivative a y| ≤ Cf
  delta_pos : 0 < delta
  delta_interval : delta ≤ (r - l) / 4
  delta_score : Cf ^ 2 * delta ^ 2 / cf ≤ 1 / 4

/-- The strict model margins imply an interior ternary interval. -/
theorem parametricTernaryConstants_exists {d : ℕ} (C : ModelConstants d) :
    Nonempty (ParametricTernaryConstants C) := by
  let s := Real.sqrt C.fourthBound
  have hC4 : 0 < C.fourthBound := lt_trans (sq_pos_of_pos C.varianceLower_pos) C.fourth_margin
  have hs : 0 < s := Real.sqrt_pos.2 hC4
  have hs2 : s ^ 2 = C.fourthBound := Real.sq_sqrt hC4.le
  have hvs : C.varianceLower < s := by nlinarith [C.fourth_margin, C.varianceLower_pos]
  let t := (C.varianceLower + s) / 2
  have hvt : C.varianceLower < t := by dsimp [t]; linarith
  have hts : t < s := by dsimp [t]; linarith
  have ht : 0 < t := lt_trans C.varianceLower_pos hvt
  let hi := min C.varianceUpper t
  have hvhi : C.varianceLower < hi := lt_min C.variance_interval hvt
  let l := C.varianceLower
  let r := (l + hi) / 2
  have hl : 0 < l := C.varianceLower_pos
  have hlr : l < r := by dsimp [r, l]; linarith
  have hrhi : r < hi := by dsimp [r, l]; linarith
  have hrt : r < t := lt_of_lt_of_le hrhi (min_le_right _ _)
  have hrU : r ≤ C.varianceUpper := le_trans hrhi.le (min_le_left _ _)
  have hr : 0 < r := lt_trans hl hlr
  let a := Real.sqrt t
  have ha : 0 < a := Real.sqrt_pos.2 ht
  have ha2 : a ^ 2 = t := Real.sq_sqrt ht.le
  have hfourth : a ^ 2 * r ≤ C.fourthBound := by
    rw [ha2]
    nlinarith [mul_pos ht (sub_pos.2 hrt)]
  let cf := min (l / (2 * a ^ 2)) (1 - r / a ^ 2)
  have ha2pos : 0 < a ^ 2 := sq_pos_of_pos ha
  have hcf : 0 < cf := by
    exact lt_min (div_pos hl (by positivity))
      (sub_pos.2 ((div_lt_one ha2pos).2 (ha2 ▸ hrt)))
  have hmass : ∀ V ∈ Icc l r, ∀ y : Fin 3, cf ≤ ternaryMass a 0 V y := by
    intro V hV y
    have hleft : cf ≤ V / (2 * a ^ 2) :=
      le_trans (min_le_left _ _) (div_le_div_of_nonneg_right hV.1 (by positivity))
    have hmid : cf ≤ 1 - V / a ^ 2 := by
      exact le_trans (min_le_right _ _) (sub_le_sub_left
        (div_le_div_of_nonneg_right hV.2 ha2pos.le) 1)
    fin_cases y <;> simpa [ternaryMass] using (by assumption)
  let Cf := 3 / a ^ 2
  have hCf : 0 < Cf := div_pos (by norm_num) ha2pos
  have hderiv : ∀ y : Fin 3, |3 * ternaryVarianceDerivative a y| ≤ Cf := by
    intro y
    have hsmall : 3 / (2 * a ^ 2) ≤ Cf := by
      dsimp [Cf]
      apply (div_le_div_iff₀ (by positivity) ha2pos).2
      nlinarith
    fin_cases y
    · change |3 * (1 / (2 * a ^ 2))| ≤ Cf
      rw [show 3 * (1 / (2 * a ^ 2)) = 3 / (2 * a ^ 2) by ring,
        abs_of_pos (div_pos (by norm_num) (by positivity))]
      exact hsmall
    · change |3 * (-1 / a ^ 2)| ≤ Cf
      rw [show 3 * (-1 / a ^ 2) = -(3 / a ^ 2) by ring, abs_neg,
        abs_of_pos (div_pos (by norm_num) ha2pos)]
    · change |3 * (1 / (2 * a ^ 2))| ≤ Cf
      rw [show 3 * (1 / (2 * a ^ 2)) = 3 / (2 * a ^ 2) by ring,
        abs_of_pos (div_pos (by norm_num) (by positivity))]
      exact hsmall
  let delta := min ((r - l) / 4) (Real.sqrt cf / (2 * Cf))
  have hdelta : 0 < delta := lt_min (div_pos (sub_pos.2 hlr) (by norm_num))
    (div_pos (Real.sqrt_pos.2 hcf) (by positivity))
  have hdeltaI : delta ≤ (r - l) / 4 := min_le_left _ _
  have hdeltaS : Cf ^ 2 * delta ^ 2 / cf ≤ 1 / 4 := by
    have hds : delta ≤ Real.sqrt cf / (2 * Cf) := min_le_right _ _
    have hprod : delta * (2 * Cf) ≤ Real.sqrt cf := (le_div_iff₀ (by positivity)).1 hds
    have hsqrt : (Real.sqrt cf) ^ 2 = cf := Real.sq_sqrt hcf.le
    have hp : 0 ≤ delta * (2 * Cf) := by positivity
    have hsq : (delta * (2 * Cf)) ^ 2 ≤ cf := by
      nlinarith [Real.sqrt_nonneg cf]
    apply (div_le_iff₀ hcf).2
    nlinarith
  exact ⟨⟨a, l, r, cf, Cf, delta, ha, hl, le_rfl, hlr, hrU,
    ha2 ▸ hrt, hfourth, hcf, hCf, hmass, hderiv, hdelta, hdeltaI, hdeltaS⟩⟩

namespace ParametricTernaryConstants

variable {d : ℕ} {C : ModelConstants d} (P : ParametricTernaryConstants C)

/-- With counting measure normalized to total mass one, the density is three
times the ternary mass.  The same positive lower guard remains valid. -/
theorem density_lower (V : ℝ) (hV : V ∈ Icc P.l P.r) (y : Fin 3) :
    P.cf ≤ 3 * ternaryMass P.a 0 V y := by
  have hmass := P.mass_lower V hV y
  have hcf := P.cf_pos
  linarith

theorem model_variance_bounds (V : ℝ) (hV : V ∈ Icc P.l P.r) :
    C.varianceLower ≤ V ∧ V ≤ C.varianceUpper :=
  ⟨le_trans P.lower_le hV.1, le_trans hV.2 P.upper_le⟩

theorem variance_lt_square_of_mem (V : ℝ) (hV : V ∈ Icc P.l P.r) :
    V < P.a ^ 2 := lt_of_le_of_lt hV.2 P.variance_lt_square

theorem fourth_le_of_mem (V : ℝ) (hV : V ∈ Icc P.l P.r) :
    P.a ^ 2 * V ≤ C.fourthBound :=
  le_trans (mul_le_mul_of_nonneg_left hV.2 (sq_nonneg _)) P.fourth_le

def varianceMinus (n : ℕ) : ℝ := (P.l + P.r) / 2 - P.delta / Real.sqrt n

def variancePlus (n : ℕ) : ℝ := (P.l + P.r) / 2 + P.delta / Real.sqrt n

theorem perturbation_nonneg (n : ℕ) : 0 ≤ P.delta / Real.sqrt n := by
  exact div_nonneg P.delta_pos.le (Real.sqrt_nonneg _)

theorem perturbation_le (n : ℕ) (hn : 1 ≤ n) :
    P.delta / Real.sqrt n ≤ P.delta := by
  have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hd := P.delta_pos
  exact div_le_self hd.le hs

theorem varianceMinus_mem (n : ℕ) (hn : 1 ≤ n) :
    P.varianceMinus n ∈ Icc P.l P.r := by
  have hnonneg := P.perturbation_nonneg n
  have hpert := P.perturbation_le n hn
  have hdelta := P.delta_interval
  have hinterval := P.interval
  constructor <;> dsimp [varianceMinus] <;> linarith

theorem variancePlus_mem (n : ℕ) (hn : 1 ≤ n) :
    P.variancePlus n ∈ Icc P.l P.r := by
  have hnonneg := P.perturbation_nonneg n
  have hpert := P.perturbation_le n hn
  have hdelta := P.delta_interval
  have hinterval := P.interval
  constructor <;> dsimp [variancePlus] <;> linarith

theorem separation (n : ℕ) :
    P.variancePlus n - P.varianceMinus n = 2 * P.delta / Real.sqrt n := by
  dsimp [varianceMinus, variancePlus]
  ring

theorem separation_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < P.variancePlus n - P.varianceMinus n := by
  rw [P.separation]
  exact div_pos (mul_pos (by norm_num) P.delta_pos)
    (Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)))

theorem quarter_separation (n : ℕ) (hn : 1 ≤ n) :
    |P.variancePlus n - P.varianceMinus n| / 4 =
      (P.delta / 2) / Real.sqrt n := by
  rw [abs_of_pos (P.separation_pos n hn), P.separation]
  ring

theorem score_budget (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * P.Cf ^ 2 * (P.variancePlus n - P.varianceMinus n) ^ 2 /
      (4 * P.cf) ≤ 1 / 4 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnp
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hnp.le
  rw [P.separation]
  have heq : (n : ℝ) * P.Cf ^ 2 * (2 * P.delta / Real.sqrt n) ^ 2 /
      (4 * P.cf) = P.Cf ^ 2 * P.delta ^ 2 / P.cf := by
    field_simp [ne_of_gt hs, ne_of_gt P.cf_pos]
    rw [hs2]
    ring
  rw [heq]
  exact P.delta_score

theorem score_budget_reverse (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * P.Cf ^ 2 * (P.varianceMinus n - P.variancePlus n) ^ 2 /
      (4 * P.cf) ≤ 1 / 4 := by
  convert P.score_budget n hn using 1 <;> ring

end ParametricTernaryConstants

end NearlyMinimax
