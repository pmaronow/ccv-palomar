module

public import NearlyMinimax.PaperLowerRegimeEnvelopes


@[expose] public section

/-! Uniform threshold tools for polynomial growth versus the regime's
quadratic logarithmic scale. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem log_quadratic_profile_div_t_tends_zero {A : ℝ} (hA : 0 < A) :
    Tendsto (fun t : ℝ => Real.log (A*t^2)/t) atTop (𝓝 0) := by
  have hf : ∀ᶠ t : ℝ in atTop, 0 < A*t^2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    positivity
  have hr : Tendsto (fun t : ℝ => (A*t^2)/t^2) atTop (𝓝 A) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [mul_div_cancel_right₀ _ (pow_ne_zero _ ht.ne')]
  exact log_profile_div_scale_tends_zero tendsto_id 2 hA hf hr

def paperRegimeSingletonEnvelope (d : ℕ) (K c0 Cs t : ℝ) : ℝ :=
  Cs*(paperLowerRegimeDegreeSlope d+1)*t*
    Real.exp (c0*((paperLowerRegimeDegreeSlope d+1)*t+1)-t^2/K)

theorem paperRegimeSingletonEnvelope_tends_zero (d : ℕ) {K c0 Cs : ℝ}
    (hK : 0 < K) (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) :
    Tendsto (paperRegimeSingletonEnvelope d K c0 Cs) atTop (𝓝 0) := by
  let A := paperLowerRegimeDegreeSlope d+1
  have hA : 0 < A := by dsimp [A]; linarith [paperLowerRegimeDegreeSlope_positive d]
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)).const_mul
    (Cs*A*Real.exp c0)
  simp only [Real.rpow_one, neg_one_mul, mul_zero] at hlim
  apply squeeze_zero' (f := paperRegimeSingletonEnvelope d K c0 Cs) _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    unfold paperRegimeSingletonEnvelope
    exact mul_nonneg (mul_nonneg (mul_nonneg hCs hA.le) ht) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (K*(c0*A+1))] with t ht hlarge
    have htK : (c0*A+1)*t ≤ t^2/K := by
      apply (le_div_iff₀ hK).mpr
      nlinarith [mul_le_mul_of_nonneg_right hlarge ht]
    have he : c0*(A*t+1)-t^2/K ≤ c0-t := by nlinarith
    have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
      (show 0 ≤ Cs*A*t by positivity)
    apply hh.trans_eq
    rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    ring

theorem PaperLowerRegime.singleton_ratio_envelope {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta c0 Cs : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) (hM : 1 ≤ M)
    (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) :
    Cs*(D : ℝ)*Real.exp (c0*((D : ℝ)+1))/N ≤
      paperRegimeSingletonEnvelope d K c0 Cs (M : ℝ) := by
  have hD := R.degree_linear hM
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one R.scale
  have hden : 0 < Real.exp ((M : ℝ)^2/K) := Real.exp_pos _
  have hA : 0 ≤ paperLowerRegimeDegreeSlope d+1 := by
    linarith [paperLowerRegimeDegreeSlope_positive d]
  have hnum : Cs*(D : ℝ)*Real.exp (c0*((D : ℝ)+1)) ≤
      Cs*((paperLowerRegimeDegreeSlope d+1)*(M : ℝ))*
        Real.exp (c0*((paperLowerRegimeDegreeSlope d+1)*(M : ℝ)+1)) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hD hCs
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith :
        (D : ℝ)+1 ≤ (paperLowerRegimeDegreeSlope d+1)*(M : ℝ)+1) hc0)
    · exact (Real.exp_pos _).le
    · have hA : 0 ≤ paperLowerRegimeDegreeSlope d+1 := by linarith [paperLowerRegimeDegreeSlope_positive d]
      positivity
  have hh := div_le_div₀ (by positivity : 0 ≤ Cs*((paperLowerRegimeDegreeSlope d+1)*(M : ℝ))*
      Real.exp (c0*((paperLowerRegimeDegreeSlope d+1)*(M : ℝ)+1)))
    hnum hden R.scale_exponential_lower
  apply hh.trans_eq
  unfold paperRegimeSingletonEnvelope
  rw [Real.exp_sub]
  ring

end NearlyMinimax
