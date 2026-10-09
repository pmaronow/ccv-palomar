module

public import NearlyMinimax.PaperLowerRegimeNumericAux


@[expose] public section

/-! Uniform numerical source hierarchy on every tuple in Reg(K).
The threshold is selected before any tuple or source state. -/
noncomputable section
open Filter Set
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def paperRegimeFineTargetBound (d : ℕ) (K c0 : ℝ) : ℕ :=
  Nat.ceil (2+2*(d : ℝ)*c0*(paperLowerRegimeDegreeSlope d+1)*K)

structure PaperRegimeHierarchy (d : ℕ) (K c0 Cact Cs : ℝ)
    (M D : ℕ) (N mu : ℝ) : Prop where
  resolution : 1 ≤ M
  cutoff : 1 < N*Real.exp (-c0*(D : ℝ))
  base : mu*(1+Real.log N) ≤ 1
  logarithm : Real.log (1+Real.log N) ≤ (M : ℝ)
  gap : 2*Real.log (1+Real.log N) < paperLowerRegimeOmega mu
  ratios : higherBandGeometricRatio d D Cact (1+Real.log N) (mu*(1+Real.log N)) 2 ≤
    higherBandGeometricRatio d D Cact (1+Real.log N) (mu*(1+Real.log N)) 1
  ratio_small : higherBandGeometricRatio d D Cact (1+Real.log N) (mu*(1+Real.log N)) 1 ≤ 1/2
  ratio_degree : (D : ℝ)^2*
    higherBandGeometricRatio d D Cact (1+Real.log N) (mu*(1+Real.log N)) 1 ≤ 1
  singleton : Cs*(D : ℝ)*Real.exp (c0*((D : ℝ)+1)) ≤ N
  target_resolution : paperRegimeFineTargetBound d K c0 ≤ M
  target_count : ∀ r : ℕ, N*Real.exp (-c0*(D : ℝ)) < higherBandTargetScale d r N mu →
    r ≤ paperRegimeFineTargetBound d K c0

theorem paperLowerRegime_uniform_hierarchy {d : ℕ} (hd : 0 < d)
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K c0 Cact Cs : ℝ) (hK : 1 ≤ K) (hc0 : 0 ≤ c0)
    (hCact : 0 ≤ Cact) (hCs : 1 ≤ Cs) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta →
      PaperRegimeHierarchy d K c0 Cact Cs M D N mu := by
  have hKp : 0 < K := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hAD : 0 < paperLowerRegimeDegreeSlope d+1 := by
    linarith [paperLowerRegimeDegreeSlope_positive d]
  have hAH : 0 < K+1 := by linarith
  have hsmall := (paperRegimeSmallBase_tends_zero hKp).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hqsmall := (paperRegimeRatioEnvelope_tends_zero hd hKp (by norm_num : (0 : ℝ)<1) Cact).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hDqsmall := (paperRegimeRatioEnvelope_square_tends_zero hd hKp (by norm_num : (0 : ℝ)<1) Cact).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlogsmall := (log_quadratic_profile_div_t_tends_zero hAH).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1/(2*K) by positivity))
  have hsingle := (paperRegimeSingletonEnvelope_tends_zero d hKp hc0 (by linarith : 0 ≤ Cs)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hnat : ∀ᶠ M : ℕ in atTop,
      1 ≤ M ∧ paperRegimeFineTargetBound d K c0 ≤ M ∧
      paperRegimeSmallBase K (M : ℝ) < 1 ∧
      paperRegimeRatioEnvelope d K Cact 1 (M : ℝ) < 1/2 ∧
      ((paperLowerRegimeDegreeSlope d+1)*(M : ℝ))^2*
        paperRegimeRatioEnvelope d K Cact 1 (M : ℝ) < 1 ∧
      Real.log ((K+1)*(M : ℝ)^2)/(M : ℝ) < 1/(2*K) ∧
      paperRegimeSingletonEnvelope d K c0 Cs (M : ℝ) < 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop (paperRegimeFineTargetBound d K c0),
      tendsto_natCast_atTop_atTop.eventually hsmall,
      tendsto_natCast_atTop_atTop.eventually hqsmall,
      tendsto_natCast_atTop_atTop.eventually hDqsmall,
      tendsto_natCast_atTop_atTop.eventually hlogsmall,
      tendsto_natCast_atTop_atTop.eventually hsingle] with M hm hr hb hq hdq hl hs
    exact ⟨hm,hr,hb,hq,hdq,hl,hs⟩
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hnat
  refine ⟨M0,?_⟩
  intro M D hM N mu eta R
  obtain ⟨hm,hr,hb,hq,hdq,hl,hs⟩ := hM0 M hM
  have hmR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hHp : 0 < 1+Real.log N := R.H_positive
  have hb0 : 0 ≤ mu*(1+Real.log N) := mul_nonneg R.occupancy_positive.le hHp.le
  have hb1 : mu*(1+Real.log N) ≤ 1 := (R.occupancy_H_envelope hm).trans hb.le
  have hlog : Real.log (1+Real.log N) < (M : ℝ)/(2*K) := by
    have hl' := (div_lt_iff₀ hmR).mp hl
    have he : Real.log ((K+1)*(M : ℝ)^2) < (M : ℝ)/(2*K) := by
      convert hl' using 1 <;> ring
    exact (Real.log_le_log hHp (R.H_polynomial hm)).trans_lt he
  have hgap : 0 < paperLowerRegimeOmega mu-Real.log (1+Real.log N) := by
    have ho := R.omega_lower
    have hmdiv : 0 < (M : ℝ)/(2*K) := by positivity
    have he : (M : ℝ)/K = 2*((M : ℝ)/(2*K)) := by ring
    rw [he] at ho
    linarith
  have hsratio := R.singleton_ratio_envelope hm hc0 (by linarith : 0 ≤ Cs)
  have hsnum : Cs*(D : ℝ)*Real.exp (c0*((D : ℝ)+1)) < N :=
    (div_lt_one (lt_of_lt_of_le zero_lt_one R.scale)).mp (hsratio.trans_lt hs)
  have hDlower : 1 ≤ D := by
    have hD := R.degree_lower
    have hslope : 2 ≤ paperLowerRegimeDegreeSlope d := by
      unfold paperLowerRegimeDegreeSlope
      linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hm
    have hDr : (1 : ℝ) ≤ D := by nlinarith
    exact_mod_cast hDr
  have hell : 1 < N*Real.exp (-c0*(D : ℝ)) := by
    have hexp : Real.exp (c0*(D : ℝ)) ≤ Cs*(D : ℝ)*Real.exp (c0*((D : ℝ)+1)) := by
      have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hDlower
      have he := Real.exp_le_exp.mpr (show c0*(D : ℝ) ≤ c0*((D : ℝ)+1) by nlinarith)
      exact he.trans (by
        have hc : (1 : ℝ) ≤ Cs*(D : ℝ) := by nlinarith only [hCs,hDr]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc
          (Real.exp_pos (c0*((D : ℝ)+1))).le)
    have hh := hexp.trans_lt hsnum
    rw [show -c0*(D : ℝ) = -(c0*(D : ℝ)) by ring, Real.exp_neg]
    exact (one_lt_div (Real.exp_pos _)).mpr hh
  refine ⟨hm,hell,hb1,?_,?_,?_,?_,?_,hsnum.le,hr,?_⟩
  · apply hlog.le.trans
    apply (div_le_self hmR.le (by linarith : 1 ≤ 2*K))
  · have ho := R.omega_lower
    have he : 2*((M : ℝ)/(2*K)) = (M : ℝ)/K := by ring
    linarith
  · unfold higherBandGeometricRatio
    apply mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (mul_pos R.occupancy_positive hHp) (R.occupancy_H_envelope hm |>.trans hb.le)
        (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hdR.le))
      (by positivity)
  · exact (R.ratio_envelope hd hm hCact (by norm_num : (0 : ℝ) ≤ 1)).trans hq.le
  · have hqr := R.ratio_envelope hd hm hCact (by norm_num : (0 : ℝ) ≤ 1)
    have he0 : 0 ≤ paperRegimeRatioEnvelope d K Cact 1 (M : ℝ) := by
      unfold paperRegimeRatioEnvelope
      positivity
    have hp := mul_le_mul (sq_le_sq₀ (Nat.cast_nonneg D) (by positivity : 0 ≤
        (paperLowerRegimeDegreeSlope d+1)*(M : ℝ)) |>.mpr (R.degree_linear hm)) hqr
      (by unfold higherBandGeometricRatio; positivity) (by positivity)
    exact hp.trans hdq.le
  · intro r hactive
    have hlogbase : Real.log (mu*(1+Real.log N)) =
        -paperLowerRegimeOmega mu+Real.log (1+Real.log N) := by
      rw [Real.log_mul R.occupancy_positive.ne' hHp.ne']
      unfold paperLowerRegimeOmega
      rw [one_div,Real.log_inv]
      ring
    have hc := fine_target_count_lt (lt_of_lt_of_le zero_lt_one R.scale)
      (mul_pos R.occupancy_positive hHp) hdR hgap hlogbase hactive
    have hden : (M : ℝ)/(2*K) ≤ paperLowerRegimeOmega mu-Real.log (1+Real.log N) := by
      have ho := R.omega_lower
      have he : (M : ℝ)/K = 2*((M : ℝ)/(2*K)) := by ring
      rw [he] at ho
      linarith
    have hrat : (d : ℝ)*c0*(D : ℝ)/(paperLowerRegimeOmega mu-Real.log (1+Real.log N)) ≤
        2*(d : ℝ)*c0*(paperLowerRegimeDegreeSlope d+1)*K := by
      apply (div_le_iff₀ hgap).mpr
      have hdlin := mul_le_mul_of_nonneg_left (R.degree_linear hm) (mul_nonneg hdR.le hc0)
      have hglin := mul_le_mul_of_nonneg_left hden
        (show 0 ≤ 2*(d : ℝ)*c0*(paperLowerRegimeDegreeSlope d+1)*K by positivity)
      have he : (2*(d : ℝ)*c0*(paperLowerRegimeDegreeSlope d+1)*K)*((M : ℝ)/(2*K)) =
          (d : ℝ)*c0*((paperLowerRegimeDegreeSlope d+1)*(M : ℝ)) := by
        field_simp [hKp.ne'] <;> ring
      rw [he] at hglin
      exact hdlin.trans hglin
    have hh : (r : ℝ) ≤ (paperRegimeFineTargetBound d K c0 : ℝ) :=
      (hc.trans_le (by linarith : 2+(d : ℝ)*c0*(D : ℝ)/
        (paperLowerRegimeOmega mu-Real.log (1+Real.log N)) ≤
        2+2*(d : ℝ)*c0*(paperLowerRegimeDegreeSlope d+1)*K)).le.trans (Nat.le_ceil _)
    exact_mod_cast hh

end NearlyMinimax
