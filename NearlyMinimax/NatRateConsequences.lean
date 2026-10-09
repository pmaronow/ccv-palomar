module

public import NearlyMinimax.Rates


@[expose] public section

/-! Analytic consequences for the paper's natural sample-size sequence. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

theorem polynomial_bounds_nat_of_rateBracket {risk : ℕ → ℝ} {lam kappa a Gamma : ℝ}
    (hk : 0 < kappa) (h : HasNatRateBracket risk lam kappa a Gamma) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*(n : ℝ)^(-lam-epsilon) ≤ risk n ∧ risk n ≤ A*(n : ℝ)^(-lam) := by
  obtain ⟨c,A,hc,hA,hb⟩ := h
  refine ⟨c,A,hc,hA,fun epsilon he => ?_⟩
  have hu := tendsto_stretched_log_factor hk (a+Gamma)
  filter_upwards [hb,tendsto_natCast_atTop_atTop.eventually
    (eventually_correction_between_powers kappa a he),
    tendsto_natCast_atTop_atTop.eventually
      (hu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))),
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
    with n hn hlow hupp hn1
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  have hp : 0 < Real.exp (-lam*Real.log n) := Real.exp_pos _
  constructor
  · apply le_trans _ hn.1
    rw [rateScale_eq_base_mul_correction]
    have hr : (n : ℝ)^(-lam-epsilon) = Real.exp (-lam*Real.log n)*(n : ℝ)^(-epsilon) := by
      rw [Real.rpow_def_of_pos hn0,Real.rpow_def_of_pos hn0,←Real.exp_add]
      congr 1
      ring
    rw [hr]
    simp only [←mul_assoc]
    exact mul_le_mul_of_nonneg_left hlow.1 (mul_pos hc hp).le
  · apply le_trans hn.2
    rw [rateScale_eq_base_mul_correction,Real.rpow_def_of_pos hn0]
    rw [mul_comm (Real.log (n : ℝ)) (-lam)]
    calc
      _ ≤ A*(Real.exp (-lam*Real.log n)*1) := by gcongr
      _ = _ := by ring

theorem normalized_risk_tends_zero_nat_of_rateBracket {risk : ℕ → ℝ} {lam kappa a Gamma : ℝ}
    (hk : 0 < kappa) (h : HasNatRateBracket risk lam kappa a Gamma) :
    Tendsto (fun n : ℕ => (n : ℝ)^lam*risk n) atTop (𝓝 0) := by
  obtain ⟨c,A,hc,hA,hb⟩ := h
  apply squeeze_zero' (g := fun n : ℕ => A*
    Real.exp (-kappa*Real.sqrt (Real.log n)+(a+Gamma)*Real.log (Real.log n)))
  · filter_upwards [hb,tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
      with n hn hn1
    have hr : 0 < risk n := (mul_pos hc (rateScale_pos _ _ _ _)).trans_le hn.1
    positivity
  · filter_upwards [hb,tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
      with n hn hn1
    have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
    have hr := mul_le_mul_of_nonneg_left hn.2 (Real.rpow_pos_of_pos hn0 lam).le
    rw [rateScale_eq_base_mul_correction,Real.rpow_def_of_pos hn0] at hr
    have he : Real.exp (Real.log (n : ℝ)*lam)*Real.exp (-lam*Real.log n)=1 := by
      rw [←Real.exp_add]
      have hz : Real.log (n : ℝ)*lam + -lam*Real.log n=0 := by ring
      rw [hz,Real.exp_zero]
    rw [Real.rpow_def_of_pos hn0]
    calc
      _ ≤ Real.exp (Real.log (n : ℝ)*lam)*(A*(Real.exp (-lam*Real.log n)*
        Real.exp (-kappa*Real.sqrt (Real.log n)+(a+Gamma)*Real.log (Real.log n)))) := hr
      _ = A*(Real.exp (Real.log (n : ℝ)*lam)*Real.exp (-lam*Real.log n))*
        Real.exp (-kappa*Real.sqrt (Real.log n)+(a+Gamma)*Real.log (Real.log n)) := by ring
      _ = _ := by rw [he]; ring
  · simpa only [Function.comp_def,mul_zero] using
      ((tendsto_stretched_log_factor hk (a+Gamma)).const_mul A).comp tendsto_natCast_atTop_atTop

end NearlyMinimax
