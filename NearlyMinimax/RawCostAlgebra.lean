module

public import NearlyMinimax.LocalEnergySeries


@[expose] public section

/-! The explicit fixed constant and factorial bookkeeping in the paper's
raw-energy lemma. All constants are chosen before the sample size. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def rawCostConstants (CB C5 C6 C7 cf ch : ℝ) : Fin 7 → ℝ :=
  ![1, C6, ch, 1 + CB ^ 2, 3 * (C5 + C7) * cf ^ 4,
    3 * C6 ^ 2 * cf ^ 4, Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2]

def rawCostConstant (CB C5 C6 C7 cf ch : ℝ) : ℝ :=
  Finset.univ.sup' (by simp) (rawCostConstants CB C5 C6 C7 cf ch)

theorem rawCostConstant_ge (CB C5 C6 C7 cf ch : ℝ) (i : Fin 7) :
    rawCostConstants CB C5 C6 C7 cf ch i ≤ rawCostConstant CB C5 C6 C7 cf ch :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem rawCostConstant_ge_one (CB C5 C6 C7 cf ch : ℝ) :
    1 ≤ rawCostConstant CB C5 C6 C7 cf ch := rawCostConstant_ge _ _ _ _ _ _ 0

theorem factorial_succ_power_le {x c C : ℝ} (hx : 0 ≤ x)
    (hc : 0 ≤ c) (hcC : c ≤ C) (m : ℕ) :
    (c * x) ^ (m + 1) ≤ c * x * (C * x) ^ m := by
  rw [pow_succ]
  have hh : (c * x) ^ m ≤ (C * x) ^ m :=
    pow_le_pow_left₀ (mul_nonneg hc hx) (mul_le_mul_of_nonneg_right hcC hx) _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (mul_nonneg hc hx)

theorem factorial_succ_energy_reduction {n v mu eta4 h4s cf c C F : ℝ}
    (hv : 0 < v) (hmu : mu = n * v) (hn : 0 ≤ n) (hcf : 0 ≤ cf)
    (hp4s : 0 ≤ h4s) (heta : eta4 = cf ^ 4 * h4s)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hF : 0 ≤ F) (m : ℕ) :
    v⁻¹ * (eta4 * F * (c * mu) ^ (m + 1) / (m + 1).factorial) ≤
      c * cf ^ 4 * n * h4s * F * (C * mu) ^ m / (m + 1).factorial := by
  have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
  have hp : (c * mu) ^ (m + 1) ≤ c * mu * (C * mu) ^ m := by
    rw [pow_succ]
    have hh : (c * mu) ^ m ≤ (C * mu) ^ m :=
      pow_le_pow_left₀ (mul_nonneg hc hmu0) (mul_le_mul_of_nonneg_right hcC hmu0) _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (mul_nonneg hc hmu0)
  calc
    _ ≤ v⁻¹ * (eta4 * F * (c * mu * (C * mu) ^ m) / (m + 1).factorial) := by
      apply mul_le_mul_of_nonneg_left
      · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_left hp
        rw [heta]
        positivity
      · positivity
    _ = _ := by rw [heta, hmu]; field_simp

theorem inverse_volume_pair_energy {n v mu eta4 h4s cf F : ℝ}
    (hv : 0 < v) (hmu : mu = n * v) (heta : eta4 = cf ^ 4 * h4s) :
    v⁻¹ * (eta4 * mu ^ 2 * F) = cf ^ 4 * (n ^ 2 * v * h4s * F) := by
  rw [heta, hmu]
  field_simp

theorem activity_plus_one_bound {B Bl CB : ℝ} (hB : 1 ≤ B)
    (hCB : 0 ≤ CB) (hBl : 0 ≤ Bl) (hcost : Bl ≤ CB * B) :
    (Bl + 1) ^ 2 ≤ (CB + 1) ^ 2 * B ^ 2 := by
  have h : Bl + 1 ≤ (CB + 1) * B := by nlinarith only [hcost, hB]
  calc
    _ ≤ ((CB + 1) * B) ^ 2 := (sq_le_sq₀ (by linarith only [hBl]) (by positivity)).mpr h
    _ = _ := mul_pow _ _ _

theorem raw_energy_cost_bound {n v mu eta4 h4s B Bl E Fdef Fal CB C5 C6 C7 cf ch : ℝ}
    (hv : 0 < v) (hmu : mu = n * v) (hn : 0 ≤ n) (hp4s : 0 ≤ h4s)
    (heta : eta4 = cf ^ 4 * h4s) (hB : 1 ≤ B) (hBl : 0 ≤ Bl)
    (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7)
    (hcf : 0 ≤ cf) (hch : 0 ≤ ch) (hFdef : 0 ≤ Fdef) (hFal : 0 ≤ Fal)
    (hcost : Bl ≤ CB * B) (M D : ℕ)
    (hE : E ≤ 3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef +
      3 * C6 * eta4 * Fal * (C6 * mu) ^ (M + 1) / (M + 1).factorial +
      Real.exp ch * eta4 * (Bl + 1) ^ 2 * (ch * mu) ^ (D + 1) / (D + 1).factorial) :
    let CG := rawCostConstant CB C5 C6 C7 cf ch
    1 + Bl ^ 2 + v⁻¹ * E ≤ CG * (B ^ 2 + n ^ 2 * v * h4s * Fdef +
      n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial +
      n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) := by
  let CG := rawCostConstant CB C5 C6 C7 cf ch
  change _ ≤ CG * _
  have hCG : 1 ≤ CG := rawCostConstant_ge_one _ _ _ _ _ _
  have hC6G : C6 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 1
  have hchG : ch ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 2
  have hBG : 1 + CB ^ 2 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 3
  have hpG : 3 * (C5 + C7) * cf ^ 4 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 4
  have haG : 3 * C6 ^ 2 * cf ^ 4 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 5
  have htG : Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2 ≤ CG :=
    rawCostConstant_ge _ _ _ _ _ _ 6
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
  have hCG0 : 0 ≤ CG := by linarith only [hCG]
  have hb2 : Bl ^ 2 ≤ CB ^ 2 * B ^ 2 := by
    calc
      _ ≤ (CB * B) ^ 2 := (sq_le_sq₀ hBl (mul_nonneg hCB hB0)).mpr hcost
      _ = _ := mul_pow _ _ _
  have hb1 : 1 ≤ B ^ 2 := by nlinarith only [hB]
  have hbase : 1 + Bl ^ 2 ≤ CG * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hBG (sq_nonneg B)
    nlinarith only [hh, hb1, hb2]
  have hp : v⁻¹ * (3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef) ≤
      CG * (n ^ 2 * v * h4s * Fdef) := by
    calc
      _ = 3 * (C5 + C7) * (cf ^ 4 * (n ^ 2 * v * h4s * Fdef)) := by
        rw [show 3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef =
          3 * (C5 + C7) * (eta4 * mu ^ 2 * Fdef) by ring, mul_left_comm,
          inverse_volume_pair_energy hv hmu heta]
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right hpG
          (by positivity : 0 ≤ n ^ 2 * v * h4s * Fdef) using 1 <;> ring
  have ha : v⁻¹ * (3 * C6 * eta4 * Fal * (C6 * mu) ^ (M + 1) / (M + 1).factorial) ≤
      CG * (n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial) := by
    have hr := factorial_succ_energy_reduction hv hmu hn hcf hp4s heta hC6 hC6G hFal M
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 3 * C6)
    apply le_trans (by convert hh using 1 <;> ring)
    convert mul_le_mul_of_nonneg_right haG
      (by positivity : 0 ≤ n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial) using 1 <;> ring
  have ht : v⁻¹ * (Real.exp ch * eta4 * (Bl + 1) ^ 2 * (ch * mu) ^ (D + 1) /
      (D + 1).factorial) ≤
      CG * (n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) := by
    have hr := factorial_succ_energy_reduction hv hmu hn hcf hp4s heta hch hchG
      (show 0 ≤ (1 : ℝ) by norm_num) D
    have hh := mul_le_mul_of_nonneg_left hr
      (by positivity : 0 ≤ Real.exp ch * (Bl + 1) ^ 2)
    have hab := activity_plus_one_bound hB hCB hBl hcost
    have hk := mul_le_mul_of_nonneg_right hab
      (by positivity : 0 ≤ Real.exp ch * ch * cf ^ 4 * n * h4s *
        (CG * mu) ^ D / (D + 1).factorial)
    apply le_trans (by convert hh using 1 <;> ring)
    apply le_trans (by convert hk using 1 <;> ring)
    convert mul_le_mul_of_nonneg_right htG
      (by positivity : 0 ≤ n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hv.le)
  nlinarith only [hscaled, hbase, hp, ha, ht]

end NearlyMinimax
