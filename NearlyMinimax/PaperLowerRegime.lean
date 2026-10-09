module

public import NearlyMinimax.SourceSaddleActivity
public import NearlyMinimax.LowSmoothnessPrior


@[expose] public section

/-! The paper's full Reg(K), as opposed to a particular saddle sequence.
Every field below is a numerical inequality from eq:LB-regime. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def paperLowerRegimeM1 {d : ℕ} (C : ModelConstants d) : ℕ :=
  Nat.ceil (4/(C.densityUpper-C.densityLower))

def paperLowerRegimeDegreeSlope (d : ℕ) : ℝ := ((d : ℝ)+8)/4

def paperLowerRegimeOmega (mu : ℝ) : ℝ := Real.log (1/mu)

structure PaperLowerRegime {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K : ℝ) (M D : ℕ) (N mu eta : ℝ) : Prop where
  regularity : 1 ≤ K
  density_resolution : paperLowerRegimeM1 C ≤ M
  degree : D = Nat.ceil (paperLowerRegimeDegreeSlope d*(M : ℝ))
  scale : 1 ≤ N
  occupancy_positive : 0 < mu
  occupancy_small : mu < 1
  omega_lower : (M : ℝ)/K ≤ paperLowerRegimeOmega mu
  omega_upper : paperLowerRegimeOmega mu ≤ K*(M : ℝ)
  logarithm_lower : (M : ℝ)^2/K ≤ Real.log N
  logarithm_upper : Real.log N ≤ K*(M : ℝ)^2
  amplitude_positive : 0 < eta
  amplitude_small : eta ≤ Q.ρ/(2 : ℝ)^(d+1)
  response_remainder : eta^(4*lowerSaddleResponseOrder C.smoothness d)*N^d ≤ 1

theorem paperLowerRegimeDegreeSlope_positive (d : ℕ) : 0 < paperLowerRegimeDegreeSlope d := by
  unfold paperLowerRegimeDegreeSlope
  positivity

theorem PaperLowerRegime.degree_lower {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) :
    paperLowerRegimeDegreeSlope d*(M : ℝ) ≤ (D : ℝ) := by
  rw [R.degree]
  exact Nat.le_ceil _

theorem PaperLowerRegime.degree_linear {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) (hM : 1 ≤ M) :
    (D : ℝ) ≤ (paperLowerRegimeDegreeSlope d+1)*(M : ℝ) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hceil := Nat.ceil_lt_add_one (mul_nonneg (paperLowerRegimeDegreeSlope_positive d).le (Nat.cast_nonneg M))
  rw [← R.degree] at hceil
  nlinarith

theorem PaperLowerRegime.H_positive {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) : 0 < 1+Real.log N := by
  linarith [Real.log_nonneg R.scale]

theorem PaperLowerRegime.H_polynomial {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) (hM : 1 ≤ M) :
    1+Real.log N ≤ (K+1)*(M : ℝ)^2 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [R.logarithm_upper]

theorem PaperLowerRegime.occupancy_exp_bound {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) : mu ≤ Real.exp (-(M : ℝ)/K) := by
  have he : mu = Real.exp (-paperLowerRegimeOmega mu) := by
    unfold paperLowerRegimeOmega
    rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr R.occupancy_positive)]
    simp
  rw [he]
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg R.omega_lower

theorem PaperLowerRegime.occupancy_H_envelope {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) (hM : 1 ≤ M) :
    mu*(1+Real.log N) ≤ (K+1)*(M : ℝ)^2*Real.exp (-(M : ℝ)/K) := by
  have h := mul_le_mul R.occupancy_exp_bound (R.H_polynomial hM)
    R.H_positive.le (Real.exp_pos _).le
  nlinarith only [h]

theorem PaperLowerRegime.scale_exponential_lower {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) :
    Real.exp ((M : ℝ)^2/K) ≤ N := by
  have h := Real.exp_le_exp.mpr R.logarithm_lower
  simpa only [Real.exp_log (lt_of_lt_of_le zero_lt_one R.scale)] using h

end NearlyMinimax
