module

public import NearlyMinimax.HighSourceNuisanceAction
public import NearlyMinimax.SourceActivationActivity
public import NearlyMinimax.CompactNuisanceNorm


@[expose] public section

/-! Separate Borel spatial dependence and actual continuous nuisance
dependence for complete marked-union numerators. Primitive source guards
are proved from the row construction, not assumed energy conclusions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

section Generic
variable {d k F n : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
  [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)
  (Q : LowSmoothnessTernaryConstants C) (η : ℝ) (j : HighWindowLabels d k)

def highUnionNuisanceNumerator (z : LocalNuisance (HighFrameIndex d F) n)
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) : ℝ :=
  affineNuisanceNumerator (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) Q.a η
    (fun e x i => highUnionSlope R j e (x i))
    (fun e _ _ => highUnionIntercept R (highCenterMix C) e)
    (highUnionResponseVector R) (highUnionResponseTime R)
    (fun x i => highPeriodicTensor d k j (x i))
    (fun x i => highLocalFrameFeature (D := F) k j (x i)) z x y

variable {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionNuisanceNumerator_measurable
    (z : LocalNuisance (HighFrameIndex d F) n) (y : Fin n → Fin 3) :
    Measurable (fun x => highUnionNuisanceNumerator C R Q η j z x y) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  apply affineNuisanceNumerator_measurable
  · exact highUnionActivation_measurable R G.activation_measurable _
  · intro i
    exact (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
  · intro i
    exact (highUnionIntercept_measurable R G.intercept_measurable _).comp measurable_snd
  · exact highUnionResponseVector_measurable R G.vector_measurable
  · exact highUnionResponseTime_measurable R G.time_measurable
  · intro i
    exact (highPeriodicTensor_contDiff d k j).continuous.measurable.comp (measurable_pi_apply i)
  · intro i γ
    exact (highLocalFrameFeature_measurable k j γ).comp (measurable_pi_apply i)

theorem highUnionNuisanceNumerator_continuousOn (hk : 2 ≤ k)
    (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2)
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
    ContinuousOn (fun z => highUnionNuisanceNumerator C R Q η j z x y)
      (localNuisanceSet (HighFrameIndex d F) n
        (C.densityLower+1/M) (C.densityUpper-1/M) Cfr Q.ρ Q.v) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  have hnumeric := high_source_interval_numeric C M G.resolution
  have hiAct : Integrable (highUnionActivation R (highCenterMix C))
      (highUnionLaw R (highCenterMix C)) := by
    apply (integrable_const (highRowTotalMass R.rowMass/highCenterMix C)).mono'
      (highUnionActivation_measurable R G.activation_measurable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun e => by
      rw [Real.norm_eq_abs]
      exact highUnionActivation_bound_nonneg R G.mass_nonneg G.total_positive
        G.activation_bound _ (highCenterMix_mem C).1 e)
  apply affineNuisanceNumerator_continuousOn _ _
    (highUnionActivation_measurable R G.activation_measurable _) hiAct
    _ _ _ _ _ _ _ hnumeric.1.le hnumeric.2.le (by linarith [G.frame])
    Q.a_pos.ne' hη hηρ
  · intro i
    exact (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
  · intro i
    exact (highUnionIntercept_measurable R G.intercept_measurable _).comp measurable_snd
  · intro e x i p hp
    exact highUnionSource_reset_interval C R G j e (x i) p hp
  · exact highUnionResponseVector_measurable R G.vector_measurable
  · intro e
    cases e with
    | inl e => exact G.vector_ball e.1 e.2
    | inr e => simp [highUnionResponseVector, inv_nonneg.mpr (by linarith [G.frame] : 0 ≤ Cfr)]
  · exact highUnionResponseTime_measurable R G.time_measurable
  · intro e
    cases e with
    | inl e => exact G.time_interval e.1 e.2
    | inr e => simp [highUnionResponseTime]
  · intro i
    exact (highPeriodicTensor_contDiff d k j).continuous.measurable.comp (measurable_pi_apply i)
  · intro x i
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j (x i))]
    exact highPeriodicTensor_le_one d k hk j (x i)
  · intro i γ
    exact (highLocalFrameFeature_measurable k j γ).comp (measurable_pi_apply i)
  · intro x c hc i
    exact highLocalFrameFeature_ball_abs_le_one k j (x i) Cfr G.frame c hc
  · intro f V hf hV y
    exact Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 y)

theorem highUnionNuisanceEnergy_measurable (hk : 2 ≤ k)
    (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2) :
    Measurable (compactNuisanceEnergy
      (localNuisanceSet (HighFrameIndex d F) n
        (C.densityLower+1/M) (C.densityUpper-1/M) Cfr Q.ρ Q.v)
      (highUnionNuisanceNumerator C R Q η j)) := by
  apply compactNuisanceEnergy_measurable
  · exact localNuisanceSet_isCompact _ _ _ _ _ _ _
  · exact localNuisanceSet_nonempty _ _
      (high_source_interval_numeric C M G.resolution).2.le
      (by linarith [G.frame]) Q.ρ_pos.le
  · intro z _ y
    exact highUnionNuisanceNumerator_measurable C R Q η j G z y
  · intro x y
    exact highUnionNuisanceNumerator_continuousOn C R Q η j G hk hη hηρ x y

theorem highUnionNuisanceEnergy_integrable_and_bound (hk : 2 ≤ k)
    (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2)
    (ν : Measure (Fin n → Covariate d)) (H : (Fin n → Covariate d) → ℝ)
    (hH : Integrable H ν)
    (hbound : ∀ z ∈ localNuisanceSet (HighFrameIndex d F) n
      (C.densityLower+1/M) (C.densityUpper-1/M) Cfr Q.ρ Q.v,
      ∀ x, (∑ y, (highUnionNuisanceNumerator C R Q η j z x y)^2) ≤ H x) :
    Integrable (compactNuisanceEnergy
      (localNuisanceSet (HighFrameIndex d F) n
        (C.densityLower+1/M) (C.densityUpper-1/M) Cfr Q.ρ Q.v)
      (highUnionNuisanceNumerator C R Q η j)) ν ∧
    (∫ x, compactNuisanceEnergy
      (localNuisanceSet (HighFrameIndex d F) n
        (C.densityLower+1/M) (C.densityUpper-1/M) Cfr Q.ρ Q.v)
      (highUnionNuisanceNumerator C R Q η j) x ∂ν) ≤ ∫ x, H x ∂ν := by
  apply compactNuisanceEnergy_integrable_and_bound
  · exact localNuisanceSet_isCompact _ _ _ _ _ _ _
  · exact localNuisanceSet_nonempty _ _
      (high_source_interval_numeric C M G.resolution).2.le
      (by linarith [G.frame]) Q.ρ_pos.le
  · intro z _ y
    exact highUnionNuisanceNumerator_measurable C R Q η j G z y
  · intro x y
    exact highUnionNuisanceNumerator_continuousOn C R Q η j G hk hη hηρ x y
  · exact hH
  · exact hbound

end Generic

section Complete
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
  (Q : LowSmoothnessTernaryConstants C) (η : ℝ) (hk : 2 ≤ k)
  (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/2) (j : HighWindowLabels d k)
include hD hq hM hCfr hℓ hℓN hk hη hηρ

theorem completeSourceNuisanceNumerator_eq_signed
    (z : LocalNuisance (HighFrameIndex d D) n)
    (hz : z ∈ localNuisanceSet (HighFrameIndex d D) n
      (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v)
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
    highUnionNuisanceNumerator C (completeSourceRows C k D M q Cfr lam ℓ N μ) Q η j z x y =
      completeSourceRawNumerator (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) lam ℓ N μ D M q Cfr Q.a z.2.2.2 η
        (fun u => highLocalCoordinates d k j (x u)) z.1 z.2.2.1
        (fun u => highPeriodicTensor d k j (x u)) z.2.1 y := by
  obtain ⟨hp,hc,hg,hV⟩ := localNuisanceSet_guards _ n _ _ _ _ _ z hz
  let φ := fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)
  let Φ := fun v : HighFrameIndex d D → ℝ =>
    highResponseProduct Q.a z.2.2.2 η z.2.2.1
      (fun u => highPeriodicTensor d k j (x u)) φ v y
  have hmΦ : Measurable Φ := highMarkedResponseProduct_measurable _ _ _ (fun v => v)
    (fun γ => measurable_pi_apply γ) _ _ _ y
  have hbΦ (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) : |Φ v| ≤ 1 := by
    apply highResponseProduct_ball_abs_le_one Cfr Q.a z.2.2.2 η Q.ρ
      Q.a_pos.ne' hη hηρ _ _ _ hg
    · intro u
      rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j (x u))]
      exact highPeriodicTensor_le_one d k hk j (x u)
    · intro v hv u
      exact highLocalFrameFeature_ball_abs_le_one k j (x u) Cfr hCfr v hv
    · intro f hf b
      exact Q.c_pos.le.trans ((Q.legal f _ hf hV).2.2.1 b)
    · exact hv
  have he := completeSourceAffineAction_eq_signed_first_action C hD hq hM
    Cfr lam ℓ N μ hCfr hℓ hℓN j x z.1 hp z.2.1 hc Φ hmΦ 1 (by norm_num) hbΦ
  unfold highUnionNuisanceNumerator affineNuisanceNumerator completeSourceRawNumerator
  apply congrArg (fun a => a - η^2*(∏ i,z.1 i)*∑ i,(highPeriodicTensor d k j (x i))^2*
    highResponseVarianceTerm Q.a z.2.2.2 η z.2.2.1
      (fun u => highPeriodicTensor d k j (x u)) φ z.2.1 y i) at he
  convert he using 1
  apply congrArg (fun t => t-η^2*(∏ i,z.1 i)*∑ i,(highPeriodicTensor d k j (x i))^2*
    highResponseVarianceTerm Q.a z.2.2.2 η z.2.2.1
      (fun u => highPeriodicTensor d k j (x u)) φ z.2.1 y i)
  apply integral_congr_ae
  filter_upwards [] with e
  unfold affineNuisanceIntegrand highUnionResponseReset Φ
  ring
  all_goals rfl

end Complete
end NearlyMinimax
