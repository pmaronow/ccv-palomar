module

public import NearlyMinimax.HighSourceNuisanceNorm
public import NearlyMinimax.HighIntrinsicLocalBounds
public import NearlyMinimax.HighUnionFisher
public import NearlyMinimax.HighSourceCanonicalResponse
public import NearlyMinimax.ExactSourceCompactEnergy


@[expose] public section

/-! Actual incoming canonical source states lie in the manuscript's exact
compact nuisance set. Their genuine local score numerators are consequently
dominated by the literal supremum-before-spatial-integration norm. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

/-- The actual density values, incoming coefficient block, WITHOUT offsets,
and physical variance at a finite configuration. -/
def sourceIncomingNuisance {d k D n : ℕ} [NeZero k]
    (η : ℝ) (p : Covariate d → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (V : ℝ)
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) :
    LocalNuisance (HighFrameIndex d D) n :=
  ((fun i => p (x i)), (c j, ((fun i => highLocalFieldWithout d k D η c j (x i)), V)))

theorem sourceIncomingNuisance_mem {d k D n : ℕ} [NeZero k]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (hk : 4 ≤ k) (ad bd Cfr η V : ℝ)
    (hCfr : highIntrinsicFrameConstant C ≤ Cfr) (hη : 0 ≤ η)
    (hηρ : η ≤ Q.ρ/(2 : ℝ)^(d+1))
    (p : Covariate d → ℝ) (hp : ∀ x, p x ∈ Icc ad bd)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (hc : ∀ l, ∑ γ, |c l γ| ≤ Cfr⁻¹)
    (hV : V ∈ Icc (Q.v-Q.ρ) Q.v) (j : HighWindowLabels d k)
    (x : Fin n → Covariate d) :
    sourceIncomingNuisance η p c V j x ∈
      localNuisanceSet (HighFrameIndex d D) n ad bd Cfr Q.ρ Q.v := by
  refine ⟨fun i => hp (x i), hc j, ?_, hV⟩
  intro i
  have h := highLocalFieldWithout_intrinsic_offset_guard C k hk Cfr η Q.ρ hCfr hη hηρ c hc j (x i)
  change -Q.ρ/2 ≤ highLocalFieldWithout d k D η c j (x i) ∧ _
  exact ⟨by simpa only [neg_div] using (abs_le.mp h).1, (abs_le.mp h).2⟩

theorem sourceLiteralAmplitude_half {d : ℕ} {ρ η : ℝ} (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/(2 : ℝ)^(d+1)) : η ≤ ρ/2 := by
  have hp : (1 : ℝ) ≤ (2 : ℝ)^d := one_le_pow₀ (by norm_num)
  apply hηρ.trans
  apply div_le_div_of_nonneg_left hρ (by norm_num : (0 : ℝ) < 2)
  rw [pow_succ]
  linarith

theorem physicalVariancePath_mem {v ρ η t : ℝ} (hηρ : η^2 ≤ ρ)
    (ht : t ∈ Icc (0 : ℝ) 1) : v-η^2*t ∈ Icc (v-ρ) v := by
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ht.2 (sq_nonneg η)]
  · nlinarith [mul_nonneg (sq_nonneg η) ht.1]

/-- The true periodic window and the chart window agree throughout the
patch, including points where the response window itself vanishes. -/
theorem highPeriodicTensor_eq_local_of_mem_patch {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) {x : Covariate d}
    (hx : x ∈ highTorusPatch d k j) :
    highPeriodicTensor d k j x = highWindowTensor d (highLocalCoordinates d k j x) := by
  obtain ⟨z,hz,hc⟩ := hx
  have he : highRawChartCoordinates d k j x = highAffineChart d k z x := by
    funext r
    unfold highRawChartCoordinates highRawChartCoordinate highAffineChart
    rw [highChartLift_eq_of_close k hk (j r) (x r) (z r) (hz r) (hc r)]
  rw [highPeriodicTensor_eq_chart_lift d k hk j x,he,
    highLocalCoordinates_eq_affine_on_patch hk j ⟨z,hz,hc⟩ z hz hc]

/-- A selected nuisance value is bounded by the actual compact maximum. -/
theorem compactNuisanceEnergy_point_le {P X Y : Type*} [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace X] [Fintype Y]
    (K : Set P) (hK : IsCompact K) (F : P → X → Y → ℝ)
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K)
    (z : P) (hz : z ∈ K) (x : X) :
    (∑ y, (F z x y)^2) ≤ compactNuisanceEnergy K F x := by
  obtain ⟨p,hp,he,hm⟩ := compactNuisanceEnergy_attained K hK ⟨z,hz⟩ F hcont x
  exact (hm z hz).trans_eq he.symm

section Complete
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
  (hk : 4 ≤ k) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ η V : ℝ)
  (hCfr : highIntrinsicFrameConstant C ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
  (hη : 0 ≤ η) (hηρ : η ≤ Q.ρ/(2 : ℝ)^(d+1))
  (hV : V ∈ Icc (Q.v-Q.ρ) Q.v)

local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
local notation "K" => localNuisanceSet (HighFrameIndex d D) n
  (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v

def completeSourceIncomingNuisance
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)))
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) :
    LocalNuisance (HighFrameIndex d D) n :=
  sourceIncomingNuisance η (highUnionSourceDensity C R h) (highUnionSourceState C R h).2 V j x

include hk hD hq hM hCfr hℓ hℓN hη hηρ hV

theorem completeSourceIncomingNuisance_mem
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)))
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) :
    completeSourceIncomingNuisance C Cfr lam ℓ N μ η V h j x ∈ K := by
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ
    ((highIntrinsicFrameConstant_ge_one C).trans hCfr) hℓ hℓN
  exact sourceIncomingNuisance_mem C Q hk _ _ Cfr η V hCfr hη hηρ
    (highUnionSourceDensity C R h) (highUnionSourceDensity_interval C R G h)
    (highUnionSourceState C R h).2 (highUnionSourceState_coefficient_ball C R G h) hV j x

theorem completeSourceRawNumerator_eq_incoming_patch
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)))
    (j : HighWindowLabels d k) (x : Fin n → Covariate d)
    (hx : ∀ i, x i ∈ highTorusPatch d k j) (y : Fin n → Fin 3) :
    highUnionSourceRawNumerator C R n Q.a V η h j x y =
      completeSourcePatchNumerator (D := D) (M := M) (q := q) C Cfr lam ℓ N μ Q η
        (completeSourceIncomingNuisance C Cfr lam ℓ N μ η V h j x)
        (highPatchProductChart d k j x) y := by
  let z := completeSourceIncomingNuisance C Cfr lam ℓ N μ η V h j x
  have hz : z ∈ K := completeSourceIncomingNuisance_mem C Q hk hD hq hM Cfr lam ℓ N μ η V
    hCfr hℓ hℓN hη hηρ hV h j x
  have hfr1 : 1 ≤ Cfr := (highIntrinsicFrameConstant_ge_one C).trans hCfr
  have heta := sourceLiteralAmplitude_half Q.ρ_pos.le hηρ
  have he := completeSourceNuisanceNumerator_eq_signed C hD hq hM Cfr lam ℓ N μ
    hfr1 hℓ hℓN Q η (by omega) hη heta j z hz x y
  have hu : highPatchProductChart d k j x ∈ sourceSpatialPatchSet d n := by
    intro i r
    exact highLocalCoordinates_abs_le_one d k j (x i) r
  have hw : (fun i : Fin n => highPeriodicTensor d k j (x i)) =
      (fun i => highWindowTensor d (highPatchProductChart d k j x i)) := by
    funext i
    exact highPeriodicTensor_eq_local_of_mem_patch hk j (hx i)
  have hcanonical : highUnionSourceRawNumerator C R n Q.a V η h j x y =
      highUnionNuisanceNumerator C R Q η j z x y := by
    unfold highUnionSourceRawNumerator highMarkedSampleNumerator highUnionNuisanceNumerator
      affineNuisanceNumerator
    apply congrArg (fun t => t-η^2*(∏ i,highUnionSourceDensity C R h (x i))*
      ∑ i,(highPeriodicTensor d k j (x i))^2*
        highResponseVarianceTerm Q.a V η
          (fun i => highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j (x i))
          (fun i => highPeriodicTensor d k j (x i))
          (fun i => highLocalFrameFeature (D := D) k j (x i))
          ((highUnionSourceState C R h).2 j) y i)
    unfold highMarkedResponseAction
    apply integral_congr_ae
    filter_upwards [] with e
    have hr (i : Fin n) : highUnionSourceResetDensity C R j h e (x i) =
        highUnionSlope R j e (x i)*highUnionSourceDensity C R h (x i)+
          highUnionIntercept R (highCenterMix C) e := by
      unfold highUnionSourceResetDensity highUnionSourceDensity
      rw [highUnionSourceState_append]
      change (if x i ∈ highTorusPatch d k j then _ else _) = _
      rw [ite_eq_left (hx i)]
    simp only [affineNuisanceIntegrand,z,completeSourceIncomingNuisance,sourceIncomingNuisance,
      highUnionSourceResetCoefficient,highUnionResponseReset,Function.comp_apply,hr]
    rfl
  rw [hcanonical,he]
  simp only [completeSourcePatchNumerator,ite_eq_left hu,z,completeSourceIncomingNuisance,sourceIncomingNuisance]
  rw [← hw]
  rfl

theorem completeSourceIncomingRawEnergy_le
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)))
    (j : HighWindowLabels d k) (x : Fin n → Covariate d)
    (hx : ∀ i, x i ∈ highTorusPatch d k j) :
    selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V η h j) x ≤
      compactNuisanceEnergy K
        (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η)
        (highPatchProductChart d k j x) := by
  have hz := completeSourceIncomingNuisance_mem C Q hk hD hq hM Cfr lam ℓ N μ η V
    hCfr hℓ hℓN hη hηρ hV h j x
  have hc := completeSourcePatchNumerator_continuousOn (n := n) C hD hq hM Cfr lam ℓ N μ
    ((highIntrinsicFrameConstant_ge_one C).trans hCfr) hℓ hℓN Q η hk hη
    (sourceLiteralAmplitude_half Q.ρ_pos.le hηρ) j
  have hs := compactNuisanceEnergy_point_le K (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ℓ N μ Q η) hc
    (completeSourceIncomingNuisance C Cfr lam ℓ N μ η V h j x) hz
    (highPatchProductChart d k j x)
  convert hs using 1
  unfold selectedRawSquareEnergy
  apply Finset.sum_congr (by ext y; simp)
  intro y _
  exact congrArg (fun t : ℝ => t^2) (completeSourceRawNumerator_eq_incoming_patch C Q hk hD hq hM
    Cfr lam ℓ N μ η V hCfr hℓ hℓN hη hηρ hV h j x hx y)

/-- Direct domination by the public actual compact spatial envelope. -/
theorem completeSourceIncomingRawEnergy_le_exactEnvelope
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)))
    (j : HighWindowLabels d k) (x : Fin n → Covariate d)
    (hx : ∀ i, x i ∈ highTorusPatch d k j) :
    selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V η h j) x ≤
      exactSourceCompactEnvelope (D := D) (M := M) (q := q)
        C Q Cfr lam ℓ N μ η n (highPatchProductChart d k j x) := by
  exact completeSourceIncomingRawEnergy_le C Q hk hD hq hM Cfr lam ℓ N μ η V
    hCfr hℓ hℓN hη hηρ hV h j x hx

end Complete
end NearlyMinimax
