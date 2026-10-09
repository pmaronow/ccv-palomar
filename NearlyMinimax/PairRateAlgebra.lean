module

public import NearlyMinimax.CommonPairRisk


@[expose] public section

/-! Numerical reduction of the exact pair-risk budget to the paper's RMS rate. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def pairFluctuationScale {d : ℕ} (n k : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ + Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)

theorem pairFluctuationScale_nonneg {d : ℕ} (n k : ℕ) :
    0 ≤ pairFluctuationScale (d := d) n k := by unfold pairFluctuationScale; positivity

theorem pairFluctuationScale_sq_lower {d : ℕ} (n k : ℕ) (hn : 0 < n) :
    1 / (n : ℝ) + (k : ℝ) ^ d / (n : ℝ) ^ 2 ≤ pairFluctuationScale (d := d) n k ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk0 : 0 ≤ (k : ℝ) ^ d := by positivity
  have ha : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = 1 / (n : ℝ) := by
    rw [inv_pow, Real.sq_sqrt hn0.le]; simp [one_div]
  have hb : (Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)) ^ 2 = (k : ℝ) ^ d / (n : ℝ) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hk0]
  have hab : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt ((k : ℝ) ^ d) / (n : ℝ)) := by positivity
  unfold pairFluctuationScale
  nlinarith

theorem pairEvaluationCoefficient_rate_le {d : ℕ} (C : ModelConstants d)
    {n m k : ℕ} (hn : 0 < n) (hm : 2 ≤ m) {c : ℝ} (hc : 0 < c)
    (hsize : c * (n : ℝ) ≤ m) :
    pairEvaluationCoefficient C m k ≤
      (C.densityUpper / c + 1 / c ^ 2) * pairFluctuationScale (d := d) n k ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hpp : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hk0 : 0 ≤ (k : ℝ) ^ d := by positivity
  have hm1 : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show m ≤ 2 * (m - 1) by omega)
  have hmsq : (c * (n : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsize 2
  have hden : c ^ 2 * (n : ℝ) ^ 2 ≤ 2 * (m : ℝ) * (m - 1 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hm1 hm0.le
    nlinarith
  have hfirst : C.densityUpper / (m : ℝ) ≤ C.densityUpper / (c * n) :=
    div_le_div_of_nonneg_left hpp (by positivity) hsize
  have hsecond : (k : ℝ) ^ d / (2 * (m : ℝ) * (m - 1 : ℕ)) ≤
      (k : ℝ) ^ d / (c ^ 2 * (n : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left hk0 (by positivity) hden
  have hA : 0 ≤ C.densityUpper / c + 1 / c ^ 2 := by positivity
  have h1 : C.densityUpper / c ≤ C.densityUpper / c + 1 / c ^ 2 := le_add_of_nonneg_right (by positivity)
  have h2 : 1 / c ^ 2 ≤ C.densityUpper / c + 1 / c ^ 2 := le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ C.densityUpper / (c * n) + (k : ℝ) ^ d / (c ^ 2 * (n : ℝ) ^ 2) :=
      add_le_add hfirst hsecond
    _ = (C.densityUpper / c) * (1 / (n : ℝ)) +
        (1 / c ^ 2) * ((k : ℝ) ^ d / (n : ℝ) ^ 2) := by ring
    _ ≤ (C.densityUpper / c + 1 / c ^ 2) *
        (1 / (n : ℝ) + (k : ℝ) ^ d / (n : ℝ) ^ 2) := by
      have ha := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 1 / (n : ℝ))
      have hb := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ (k : ℝ) ^ d / (n : ℝ) ^ 2)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (pairFluctuationScale_sq_lower n k hn) hA

def pairRateSquaredConstant {d : ℕ} (C : ModelConstants d) (Cp c a : ℝ) : ℝ :=
  (2 / a ^ 2) *
    ((4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper) *
      (4 * (C.densityUpper / c + 1 / c ^ 2) * (1 + Cp) ^ 4) +
    (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) *
      (2 * C.densityUpper * (1 + Cp) ^ 4) + C.densityUpper ^ 2 / 2)

theorem pairRateSquaredConstant_pos {d : ℕ} (C : ModelConstants d)
    {Cp c a : ℝ} (hCp : 0 ≤ Cp) (hc : 0 < c) (ha : 0 < a) :
    0 < pairRateSquaredConstant C Cp c a := by
  have hpp : 0 < C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hEB := responseOperatorEnergyBound_pos C
  unfold pairRateSquaredConstant
  positivity

theorem pairRiskBudget_rate_le {d : ℕ} (C : ModelConstants d)
    {n m k : ℕ} (hn : 0 < n) (hm : 2 ≤ m) {Cp W lam B b c a : ℝ}
    (hCp : 0 ≤ Cp) (hW : 0 ≤ W) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (hc : 0 < c) (ha : 0 < a) (hsize : c * (n : ℝ) ≤ m)
    (hlamBudget : lam ≤ Cp ^ 2 * W / n)
    (hBBudget : B ≤ C.densityUpper * (2 * Cp ^ 2 + Cp * W)) :
    pairRiskBudget C m k Cp W lam B b a ≤ pairRateSquaredConstant C Cp c a *
      (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W)) ^ 2 := by
  let P := 1 + Cp
  let t := pairFluctuationScale (d := d) n k
  let R := t * (1 + W)
  let E := C.densityUpper / c + 1 / c ^ 2
  let F := 2 * Cp ^ 2 + 2 * Cp * W
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpp : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hEB := (responseOperatorEnergyBound_pos C).le
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have ht : 0 ≤ t := pairFluctuationScale_nonneg n k
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hCP : Cp ≤ P ^ 2 := by dsimp [P]; nlinarith only [hCp, sq_nonneg Cp]
  have hC2P : Cp ^ 2 ≤ P ^ 2 := by dsimp [P]; nlinarith only [hCp]
  have hCW := mul_le_mul_of_nonneg_right hCP hW
  have hFb : F ≤ 2 * P ^ 2 * (1 + W) := by dsimp [F]; nlinarith only [hC2P, hCW]
  have hF2 : F ^ 2 ≤ 4 * P ^ 4 * (1 + W) ^ 2 := by
    apply (pow_le_pow_left₀ hF hFb 2).trans_eq
    ring
  have he := pairEvaluationCoefficient_rate_le (k := k) C hn hm hc hsize
  have hEt : 0 ≤ pairEvaluationCoefficient C m k := by unfold pairEvaluationCoefficient; positivity
  have hEF : pairEvaluationCoefficient C m k * F ^ 2 ≤ 4 * E * P ^ 4 * R ^ 2 := by
    have h := mul_le_mul he hF2 (sq_nonneg F) (by positivity)
    apply h.trans_eq
    dsimp only [E, t, R]
    ring
  have hBb : B ≤ 2 * C.densityUpper * P ^ 2 * (1 + W) := by
    have h := mul_le_mul_of_nonneg_left (show 2 * Cp ^ 2 + Cp * W ≤ 2 * P ^ 2 * (1 + W) by nlinarith only [hC2P, hCW, mul_nonneg (sq_nonneg P) hW]) hpp
    apply (hBBudget.trans h).trans_eq
    ring
  have hLamSmall : lam ≤ P ^ 2 * W / (n : ℝ) := by
    exact hlamBudget.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2P hW) hn0.le)
  have hLamB : lam * B ≤ 2 * C.densityUpper * P ^ 4 * R ^ 2 := by
    have hmB := mul_le_mul hLamSmall hBb hB (by positivity : 0 ≤ P ^ 2 * W / (n : ℝ))
    have hW2 : W * (1 + W) ≤ (1 + W) ^ 2 := by nlinarith only [hW]
    have ht2 : 1 / (n : ℝ) ≤ t ^ 2 := by
      have h := pairFluctuationScale_sq_lower (d := d) n k hn
      have hk0 : 0 ≤ (k : ℝ) ^ d / (n : ℝ) ^ 2 := by positivity
      dsimp [t]
      linarith
    calc
      _ ≤ (P ^ 2 * W / (n : ℝ)) * (2 * C.densityUpper * P ^ 2 * (1 + W)) := hmB
      _ = (2 * C.densityUpper * P ^ 4) * (W * (1 + W)) * (1 / (n : ℝ)) := by ring
      _ ≤ (2 * C.densityUpper * P ^ 4) * (1 + W) ^ 2 * (1 / (n : ℝ)) := by gcongr
      _ ≤ (2 * C.densityUpper * P ^ 4) * (1 + W) ^ 2 * t ^ 2 := by gcongr
      _ = _ := by dsimp [R]; ring
  have hA0 : 0 ≤ 4 * responseOperatorEnergyBound C * C.densityUpper +
      8 * C.varianceUpper ^ 2 * C.densityUpper := by positivity
  have hL0 : 0 ≤ 3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2 := by positivity
  have hER := mul_le_mul_of_nonneg_left hEF hA0
  have hLR := mul_le_mul_of_nonneg_left hLamB hL0
  have hsR : R ^ 2 ≤ (b ^ 2 + R) ^ 2 :=
    pow_le_pow_left₀ hR (le_add_of_nonneg_left (sq_nonneg b)) 2
  have hsb : b ^ 4 ≤ (b ^ 2 + R) ^ 2 := by
    have hh := pow_le_pow_left₀ (sq_nonneg b) (le_add_of_nonneg_right hR) 2
    simpa only [← pow_mul] using hh
  have hCR : 0 ≤ (4 * responseOperatorEnergyBound C * C.densityUpper +
      8 * C.varianceUpper ^ 2 * C.densityUpper) * (4 * E * P ^ 4) +
      (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) *
        (2 * C.densityUpper * P ^ 4) := by positivity
  have hCsb := mul_le_mul_of_nonneg_left hsb (by positivity : 0 ≤ C.densityUpper ^ 2 / 2)
  have hCsR := mul_le_mul_of_nonneg_left hsR hCR
  have hbudget : pairRiskBudget C m k Cp W lam B b a =
      (2 / a ^ 2) *
        ((4 * responseOperatorEnergyBound C * C.densityUpper + 8 * C.varianceUpper ^ 2 * C.densityUpper) *
          (pairEvaluationCoefficient C m k * F ^ 2) +
        (3 * (2 * C.holderBound ^ 2 + 1) ^ 2 + 6 * C.varianceUpper ^ 2) * (lam * B) +
        (C.densityUpper ^ 2 / 2) * b ^ 4) := by unfold pairRiskBudget F; ring
  rw [hbudget]
  unfold pairRateSquaredConstant
  change (2 / a ^ 2) * _ ≤ (2 / a ^ 2) * _ * (b ^ 2 + R) ^ 2
  rw [mul_assoc (2 / a ^ 2) _ ((b ^ 2 + R) ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 / a ^ 2)
  dsimp only [E, P] at hER hLR hCsR hCsb
  linarith only [hER, hLR, hCsR, hCsb]

end NearlyMinimax
