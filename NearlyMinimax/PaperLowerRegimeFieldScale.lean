module

public import NearlyMinimax.PaperLowerRegimeSource
public import NearlyMinimax.FineFieldScaleBudget


@[expose] public section

/-! Uniform higher-field scale absorption for every tuple in Reg(K).
The quadratic lower bound on log N dominates the linear M/D terms. -/
noncomputable section
open Filter
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def paperRegimeFieldLinearConstant (d : ℕ) (c0 : ℝ) : ℝ :=
  2*c0+c0*(2*(d : ℝ)-4)*(paperLowerRegimeDegreeSlope d+1)

theorem PaperLowerRegime.field_profile_le_one {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta c0 tau : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) (hd : 4 < d) (hM : 1 ≤ M)
    (hc0 : 0 ≤ c0) (htau : tau ≤ c0)
    (hbudget : paperRegimeFieldLinearConstant d c0 ≤ ((d : ℝ)-4)*(M : ℝ)/K) :
    Real.exp (2*tau*M)*N^(4-(d : ℝ))*Real.exp (c0*(2*(d : ℝ)-4)*D) ≤ 1 := by
  have hdR : (4 : ℝ) < d := by exact_mod_cast hd
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one R.scale
  have hT := mul_le_mul_of_nonneg_right htau (by positivity : 0 ≤ (2 : ℝ)*M)
  have hL := mul_le_mul_of_nonneg_left R.logarithm_lower (by linarith : 0 ≤ (d : ℝ)-4)
  have hL' : ((d : ℝ)-4)*(M : ℝ)^2/K ≤ ((d : ℝ)-4)*Real.log N := by
    convert hL using 1 <;> ring
  have hdim : 0 ≤ 2*(d : ℝ)-4 := by linarith only [hdR]
  have hD := mul_le_mul_of_nonneg_left (R.degree_linear hM)
    (mul_nonneg hc0 hdim)
  have hB := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg M)
  have hB' : paperRegimeFieldLinearConstant d c0*M ≤ ((d : ℝ)-4)*(M : ℝ)^2/K := by
    convert hB using 1 <;> ring
  rw [Real.rpow_def_of_pos hN,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  unfold paperRegimeFieldLinearConstant at hB'
  nlinarith only [hT,hL',hD,hB']

theorem paperLowerRegime_uniform_field_scale {d : ℕ} (hd : 4 < d)
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (K : ℝ) (hK : 1 ≤ K) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta →
      let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
      let ell := N*Real.exp (-c0*D)
      Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M)*mu^4*ell^(4-2*(d : ℝ)) ≤
        mu^2*N^(-(d : ℝ)) ∧
      Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M)*mu^4*(ell^(2-(d : ℝ)))^2 ≤
        mu^2*N^(-(d : ℝ)) := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  have hc0 : 0 < c0 := by dsimp [c0]; linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hdR : (4 : ℝ) < d := by exact_mod_cast hd
  let B := K*paperRegimeFieldLinearConstant d c0/((d : ℝ)-4)
  obtain ⟨Mt,hMt⟩ := eventually_atTop.mp
    (shrunkDensityExponent_eventually_le_plus_one C.densityLower_pos hab)
  let M0 := max Mt (max 1 (Nat.ceil B))
  refine ⟨M0,?_⟩
  intro M D hM N mu eta R
  have hMtM : Mt ≤ M := (le_max_left _ _).trans hM
  have hM1 : 1 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hceil : Nat.ceil B ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hB : B ≤ (M : ℝ) := (Nat.le_ceil B).trans (by exact_mod_cast hceil)
  have hbudget : paperRegimeFieldLinearConstant d c0 ≤ ((d : ℝ)-4)*(M : ℝ)/K := by
    apply (le_div_iff₀ hKp).mpr
    have h := (div_le_iff₀ (by linarith : 0 < (d : ℝ)-4)).mp hB
    try dsimp only [B] at h
    nlinarith only [h]
  have hprofile := R.field_profile_le_one hd hM1 hc0.le (hMt M hMtM) hbudget
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one R.scale
  have he := fine_field_scale_absorption hN R.occupancy_positive.le R.occupancy_small.le
    (ell := N*Real.exp (-c0*D)) rfl hprofile
  dsimp only
  refine ⟨he,?_⟩
  have hpow : ((N*Real.exp (-c0*D))^(2-(d : ℝ)))^2 =
      (N*Real.exp (-c0*D))^(4-2*(d : ℝ)) := by
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ N*Real.exp (-c0*D))]
    congr 1
    ring
  rw [hpow]
  exact he

end NearlyMinimax
