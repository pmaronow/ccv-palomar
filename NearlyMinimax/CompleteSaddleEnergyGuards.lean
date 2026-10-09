module

public import NearlyMinimax.CompleteSourceSaddleRegime
public import NearlyMinimax.LowerSaddleDegreeBounds
public import NearlyMinimax.FineFieldScaleBudget


@[expose] public section

/-! Every scalar guard used in the complete-source factorial energy bound
is a conclusion of the actual rounded saddle. Constants precede its shift
and sample size; no energy, regularity or desired-rate guard is assumed. -/
noncomputable section
open Filter Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev completeSaddleM {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleM (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleD d (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleN {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleN C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleMu {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x
abbrev completeSaddleEta {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) :=
  lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf x
abbrev completeSaddleC0 {d : ℕ} (C : ModelConstants d) :=
  densityIntervalExponent C.densityLower C.densityUpper+1
abbrev completeSaddleEll {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (completeSaddleC0 C)
    (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleTau {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  shrunkDensityExponent C.densityLower C.densityUpper (completeSaddleM C x)
abbrev completeSaddleAD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityLower+1/(completeSaddleM C x : ℝ)
abbrev completeSaddleBD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityUpper-1/(completeSaddleM C x : ℝ)

structure CompleteSaddleEnergyGuards {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) : Prop where
  resolution : highCenterResolutionThreshold C ≤ (completeSaddleM C x : ℝ)
  resolution_one : 1 ≤ (completeSaddleM C x : ℝ)
  N_one : 1 ≤ completeSaddleN C Cω x
  mu_positive : 0 < completeSaddleMu C Cω x
  mu_one : completeSaddleMu C Cω x ≤ 1
  mu_log : completeSaddleMu C Cω x*(1+Real.log (completeSaddleN C Cω x)) ≤ 1
  eta_positive : 0 < completeSaddleEta C Cω cf x
  response_taylor : (completeSaddleEta C Cω cf x)^(4*lowerSaddleResponseOrder C.smoothness d)*
    (completeSaddleN C Cω x)^d ≤ 1
  tau_nonneg : 0 ≤ completeSaddleTau C x
  tau_le : completeSaddleTau C x ≤ completeSaddleC0 C
  degree_multiple : (completeSaddleD C x : ℝ) ≤
    (((d : ℝ)+8)/4+1)*(completeSaddleM C x : ℝ)
  ell_one : 1 ≤ completeSaddleEll C Cω x
  ell_lt_N : completeSaddleEll C Cω x < completeSaddleN C Cω x
  field_scale : Real.exp (2*completeSaddleTau C x*(completeSaddleM C x : ℝ))*
    (completeSaddleMu C Cω x)^4*(completeSaddleEll C Cω x)^(4-2*(d : ℝ)) ≤
      (completeSaddleMu C Cω x)^2*(completeSaddleN C Cω x)^(-(d : ℝ))
  field_scale_square : Real.exp (2*completeSaddleTau C x*(completeSaddleM C x : ℝ))*
    (completeSaddleMu C Cω x)^4*((completeSaddleEll C Cω x)^(2-(d : ℝ)))^2 ≤
      (completeSaddleMu C Cω x)^2*(completeSaddleN C Cω x)^(-(d : ℝ))
  ad_ge : C.densityLower ≤ completeSaddleAD C x
  bd_nonneg : 0 ≤ completeSaddleBD C x
  bd_le : completeSaddleBD C x ≤ C.densityUpper
  ad_positive : 0 < completeSaddleAD C x
  density_interval : completeSaddleAD C x < completeSaddleBD C x

 theorem eventually_completeSaddleEnergyGuards {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf : ℝ} (hcf : 0 < cf) (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop, CompleteSaddleEnergyGuards C Cω cf n := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := densityIntervalExponent C.densityLower C.densityUpper
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau : 0 < tau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  obtain ⟨K,_,hreg⟩ := completeSourceSaddle_fixed_regime_window C hs hd hcf
  have hhier := actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd
    C.densityLower_pos hab (by norm_num) (by norm_num) Cω
  have hscale := eventually_lowerSaddle_fine_field_energy_scale hs hd hm htheta hcontrol Cω (tau+1)
  have hparams := eventually_completeSourceSaddle_parameters C hs hd hcf
    (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1) Cω
  filter_upwards [hreg Cω 1 0 (by norm_num),tendsto_natCast_atTop_atTop.eventually hhier,
    tendsto_natCast_atTop_atTop.eventually hscale,
    tendsto_natCast_atTop_atTop.eventually hparams,
    tendsto_natCast_atTop_atTop.eventually
      ((lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop (1 : ℝ)))]
    with n hregn hhiern hscalen hpn hMone
  change LowerSaddleReg K 1 C.smoothness d m theta Cω cf 0
    (shrunkDensityExponent C.densityLower C.densityUpper) n at hregn
  rcases hregn with ⟨_,_,hN,hmu,hmu1,_,_,_,_,heta,_,hqt⟩
  change LowerAliasHierarchy C.smoothness d m theta Cω 1 1 (tau+1)
    (shrunkDensityExponent C.densityLower C.densityUpper) n at hhiern
  rcases hhiern with ⟨hell,htaule,hmulog,_,_,_,_,_,_,_,_,_⟩
  dsimp only at hpn
  obtain ⟨had,hadb⟩ := high_source_interval_numeric C (completeSaddleM C n : ℝ) hpn.2.2.1
  have htn : 0 ≤ completeSaddleTau C n := by
    have hi : C.densityLower+(completeSaddleM C n : ℝ)⁻¹ <
        C.densityUpper-(completeSaddleM C n : ℝ)⁻¹ := by simpa only [one_div] using hadb
    have hia : 0 < C.densityLower+(completeSaddleM C n : ℝ)⁻¹ := by simpa only [one_div] using had
    exact (densityIntervalExponent_pos hia hi).le
  have hfield : Real.exp (2*completeSaddleTau C n*(completeSaddleM C n : ℝ))*
      (completeSaddleMu C Cω n)^4*(completeSaddleEll C Cω n)^(4-2*(d : ℝ)) ≤
      (completeSaddleMu C Cω n)^2*(completeSaddleN C Cω n)^(-(d : ℝ)) := hscalen
  have hsquare : ((completeSaddleEll C Cω n)^(2-(d : ℝ)))^2 =
      (completeSaddleEll C Cω n)^(4-2*(d : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by linarith only [hell] : 0 ≤ completeSaddleEll C Cω n)]
    congr 1
    ring
  refine ⟨hpn.2.2.1,hMone,hN,hmu,hmu1.le,hmulog,heta,?_,htn,htaule,
    lowerSaddleD_le_fixed_multiple (Nat.cast_nonneg _) hMone,hell.le,hpn.2.2.2.2.1,
    hfield,?_,?_,had.le.trans hadb.le,?_,had,hadb⟩
  · simpa only [lowerSaddleResponseQuantity,Real.rpow_natCast] using hqt
  · rw [hsquare]
    exact hfield
  · dsimp only [completeSaddleAD]
    exact le_add_of_nonneg_right (one_div_nonneg.mpr (Nat.cast_nonneg _))
  · dsimp only [completeSaddleBD]
    exact sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg _))

end NearlyMinimax
