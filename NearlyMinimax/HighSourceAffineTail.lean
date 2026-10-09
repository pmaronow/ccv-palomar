module

public import NearlyMinimax.HighSourceNuisanceAction
public import NearlyMinimax.HighUnionNuisanceRegularity


@[expose] public section

/-! Genuine all-count response Taylor bounds for the actual complete tagged
source with arbitrary legal incoming density and coefficient nuisance values. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
section Complete
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
include hD hq hM hCfr hℓ hℓN
theorem completeSourceAffineResponseAction_all_count_bound (hn : 1 ≤ n)
    (j : HighWindowLabels d k)
    (p : Fin n → ℝ)
    (hpIn : ∀ u, p u ∈ Icc (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)))
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ Cfr⁻¹)
    (a V η ρ : ℝ) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (x : Fin n → Covariate d) (g w : Fin n → ℝ)
    (φ : Fin n → HighFrameIndex d D → ℝ)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ Cfr⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e)
      (fun e => highUnionResponseReset R e c) g w φ y| ≤
      (C.densityUpper^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        highRowTotalMass (R).rowMass := by
  let ad := C.densityLower+1/(M : ℝ)
  let bd := C.densityUpper-1/(M : ℝ)
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  have hCf : 0 < Cfr := by linarith
  obtain ⟨had,hadbd⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq ad bd had hadbd Cfr hCf
    lam ℓ N μ hℓ hℓN
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) :=
    highUnionMark_standardBorel
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  let reset : (i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ) →
      SourceRowDensityMark d D M q ad bd Cfr lam ℓ N μ i → Fin n → ℝ :=
    fun i z u => highUnionSlope R j (Sum.inl ⟨i,sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i z⟩) (x u)*p u+
      highUnionIntercept R (highCenterMix C) (Sum.inl ⟨i,sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i z⟩)
  have hresetMeas (i) (u) : Measurable (fun z => reset i z u) := by
    let emb : SourceRowDensityMark d D M q ad bd Cfr lam ℓ N μ i → HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ) := fun z : SourceRowDensityMark d D M q ad bd Cfr lam ℓ N μ i =>
      Sum.inl ⟨i,sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i z⟩
    have he : Measurable emb := measurable_inl.comp ((rowSigmaMk_measurable i).comp
      (sourceRowDensityLift_measurable d D M q ad bd Cfr lam ℓ N μ r₀ i))
    exact (((highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (he.prodMk measurable_const)).mul_const (p u)).add
      ((highUnionIntercept_measurable R G.intercept_measurable _).comp he)
  have hresetBound (i) (z) (u) : |reset i z u| ≤ C.densityUpper := by
    have hh := highUnionSource_reset_interval C R G j
      (Sum.inl ⟨i,sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i z⟩) (x u) (p u) (hpIn u)
    rw [abs_of_nonneg (C.densityLower_pos.le.trans (by linarith [hh.1,one_div_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ)≤M)]))]
    linarith [hh.2,one_div_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ)≤M)]
  have hirrel (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSlope R j (Sum.inl ⟨i,e⟩) (x u)*p u+highUnionIntercept R (highCenterMix C) (Sum.inl ⟨i,e⟩) =
      reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e) u := by
    simp only [reset,highUnionSlope,highUnionIntercept,highCenteredRowUnionSlope,highCenteredRowUnionIntercept,balancedSlope,balancedIntercept,Sum.elim_inl,completeSourceRows]
    rw [sourceRow_density_projection_slope d k D M q ad bd Cfr lam ℓ N μ r₀ j i e (x u),
      sourceRow_density_projection_intercept d k D M q ad bd Cfr lam ℓ N μ r₀ i e]
  let O := fun e => (∏ u, (highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e))*
    highResponseProduct a V η g w φ (highUnionResponseReset R e c) y
  have hcoef : Measurable (fun e => highUnionResponseReset R e c) := by
    apply measurable_pi_iff.mpr
    intro γ
    unfold highUnionResponseReset coefficientReset
    exact (measurable_const.sub (highUnionResponseTime_measurable R G.time_measurable)).mul
      measurable_const |>.add ((highUnionResponseTime_measurable R G.time_measurable).mul
        (highUnionResponseVector_measurable R G.vector_measurable γ))
  have hmO : Measurable O := (Finset.measurable_fun_prod _ (fun u _ =>
    (((highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_id.prodMk measurable_const)).mul_const (p u)).add
      (highUnionIntercept_measurable R G.intercept_measurable _))).mul
        (highMarkedResponseProduct_measurable a V η _
          (fun γ => (measurable_pi_apply γ).comp hcoef) g w φ y)
  have hOb (e) : ‖O e‖ ≤ C.densityUpper^n := by
    have hcReset := highUnionResponseReset_ball R Cfr hCf G.vector_ball G.time_interval e c hc
    have hResponse := highResponseProduct_ball_abs_le_one Cfr a V η ρ ha.ne' hη hηρ
      g w φ hg hw hφ hp _ hcReset y
    change |(∏ u, (highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e))*highResponseProduct a V η g w φ _ y| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ C.densityUpper (lt_trans zero_lt_one C.one_lt_densityUpper).le
      (fun u => by
        have hh := highUnionSource_reset_interval C R G j e (x u) (p u) (hpIn u)
        rw [abs_of_nonneg (by linarith [hh.1,C.densityLower_pos,one_div_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ)≤M)])]
        linarith [hh.2,one_div_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ)≤M)])) hResponse
        (abs_nonneg _) (pow_nonneg (lt_trans zero_lt_one C.one_lt_densityUpper).le _)).trans_eq (mul_one _)
  have he : highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e)
      (fun e => highUnionResponseReset R e c) g w φ y =
      ∑ i, highMarkedResponseAction ((R).rowLaw i) ((R).rowActivation i) a V η
        (fun e => reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e))
        (fun e => coefficientReset c ((R).rowVector i e) ((R).rowTime i e)) g w φ y := by
    unfold highMarkedResponseAction
    simp_rw [mul_assoc]
    rw [highUnionSource_bounded_action C R G hpos O hmO (C.densityUpper^n) hOb]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with e
    simp only [O,hirrel,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ =>
    sourceRow_reference_all_count_bound d k D M q hn ad bd Cfr lam ℓ N μ a V η ρ C.densityUpper
      hCf ha hη hρ hηρ (lt_trans zero_lt_one C.one_lt_densityUpper).le hpos i (reset i) (hresetMeas i) (hresetBound i)
      g w φ c hc hg hw hφ hp y)).trans_eq
  exact (Finset.mul_sum _ _ _).symm


theorem completeSourceAffineNumerator_all_count_exponential_bound (hn : 1 ≤ n)
    (j : HighWindowLabels d k)
    (p : Fin n → ℝ)
    (hpIn : ∀ u, p u ∈ Icc (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)))
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ Cfr⁻¹)
    (a V η ρ : ℝ) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (x : Fin n → Covariate d) (g w : Fin n → ℝ)
    (φ : Fin n → HighFrameIndex d D → ℝ)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ Cfr⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      p
      (fun e u => highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e)
      (fun e => highUnionResponseReset R e c) g w φ c y| ≤
      (highSeparatedScoreExponentialConstant a ρ C.densityUpper 1 1)^n *
        η^2*(highRowTotalMass (R).rowMass+1) := by
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  let B := highRowTotalMass (R).rowMass
  have hpCurrent (u) (b) : 0 ≤ ternaryMass a (coefficientRegression η g w φ c u) V b := by
    apply hp _
    have hv := hφ c hc u
    change |g u+η*w u*(∑ γ, φ u γ*c γ)| ≤ ρ
    have hh : |η*w u*(∑ γ, φ u γ*c γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hη]
      have ht := mul_le_mul (hw u) hv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left ht hη]
    exact (abs_add_le _ _).trans (by linarith [hg u])
  have hIncoming (u) : |p u| ≤ C.densityUpper := by
    rw [abs_of_nonneg (by linarith [(hpIn u).1,C.densityLower_pos,one_div_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ)≤M)])]
    linarith [(hpIn u).2,one_div_nonneg.mpr (Nat.cast_nonneg M : (0:ℝ)≤M)]
  have haction := completeSourceAffineResponseAction_all_count_bound C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN hn j p hpIn c hc a V η ρ ha hη hρ hηρ x g w φ hg hw hφ hp y
  have hcorrection := high_response_variance_correction_abs_bound hn a V η C.densityUpper
    ha (lt_trans zero_lt_one C.one_lt_densityUpper).le p g w φ c
    hw hIncoming hpCurrent y
  have hraw : |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      p
      (fun e u => highUnionSlope R j e (x u)*p u+highUnionIntercept R (highCenterMix C) e)
      (fun e => highUnionResponseReset R e c) g w φ c y| ≤
      C.densityUpper^n*(highSeparatedDerivativeBudget a ρ*B+1/a^2)*(n : ℝ)^2*η^2 := by
    unfold highMarkedLocalScoreNumerator
    apply (abs_sub _ _).trans
    apply (add_le_add haction hcorrection).trans_eq
    dsimp [B]
    ring
  apply hraw.trans
  simpa only [mul_one,div_one] using highSeparated_score_budget_absorb n hn a ρ C.densityUpper
    1 1 η B (lt_trans zero_lt_one C.one_lt_densityUpper).le (by norm_num) (by norm_num) G.total_positive.le


theorem completeSourceNuisanceNumerator_all_count_bound (hn : 1 ≤ n)
    (Q : LowSmoothnessTernaryConstants C) (η : ℝ) (hk : 2 ≤ k)
    (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2)
    (j : HighWindowLabels d k) (z : LocalNuisance (HighFrameIndex d D) n)
    (hz : z ∈ localNuisanceSet (HighFrameIndex d D) n
      (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v)
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
    |highUnionNuisanceNumerator C R Q η j z x y| ≤
      (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)^n*
        η^2*(highRowTotalMass (R).rowMass+1) := by
  obtain ⟨hp,hc,hg,hV⟩ := localNuisanceSet_guards _ n _ _ _ _ _ z hz
  have hh := completeSourceAffineNumerator_all_count_exponential_bound C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN hn j z.1 hp z.2.1 hc Q.a z.2.2.2 η Q.ρ Q.a_pos hη Q.ρ_pos.le hηρ x
    z.2.2.1 (fun u => highPeriodicTensor d k j (x u)) (fun u => highLocalFrameFeature k j (x u))
    hg (fun u => by
      rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j (x u))]
      exact highPeriodicTensor_le_one d k hk j (x u))
    (fun v hv u => highLocalFrameFeature_ball_abs_le_one k j (x u) Cfr hCfr v hv)
    (fun f hf y => Q.c_pos.le.trans ((Q.legal f z.2.2.2 hf hV).2.2.1 y)) y
  simpa only [highUnionNuisanceNumerator,affineNuisanceNumerator,affineNuisanceIntegrand,
    highMarkedLocalScoreNumerator,highMarkedResponseAction,highUnionResponseReset,mul_assoc] using hh

end Complete
end NearlyMinimax
