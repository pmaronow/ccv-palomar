module

public import NearlyMinimax.HighSourceCanonicalAction


@[expose] public section

/-! Exact equality of the actual canonical likelihood numerator and the
complete signed-row numerator used in the count decomposition. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1300000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

section
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)))
    (x : Fin n → Covariate d) (hx : ∀ u, x u ∈ highTorusPatch d k j)
    (a V η : ℝ) (ha : a ≠ 0) (g w : Fin n → ℝ)

local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
local notation "U" => fun u : Fin n => highLocalCoordinates d k j (x u)

variable (hp : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ Cfr⁻¹ → ∀ u b,
    0 ≤ ternaryMass a (coefficientRegression η g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) v u) V b)
include hD hq hM hCfr hℓ hℓN hx ha hp

theorem completeSourceResponseAction_eq_signed_first_action (y : Fin n → Fin 3) :
    highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) y =
      completeSourceSignedFirstAction (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) lam ℓ N μ D M q Cfr U
        (fun u => highUnionSourceDensity C R h (x u)) ((highUnionSourceState C R h).2 j)
        (fun v => highResponseProduct a V η g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) v y) := by
  let Φ := fun v : HighFrameIndex d D → ℝ => highResponseProduct a V η g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) v y
  have hmΦ : Measurable Φ := highMarkedResponseProduct_measurable a V η (fun v => v)
    (fun γ => measurable_pi_apply γ) g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) y
  have hbΦ (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) : |Φ v| ≤ 1 :=
    highMarkedResponseProduct_abs_le_one a V η ha g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) v (hp v hv) y
  have he := completeSourceCanonicalAction_eq_signed_first_action C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN j h x hx Φ hmΦ 1 (by norm_num) hbΦ
  apply Eq.trans _ he
  unfold highMarkedResponseAction
  apply integral_congr_ae
  filter_upwards [] with e
  dsimp only [Φ]
  ring

theorem completeSourceRawNumerator_eq_canonical (y : Fin n → Fin 3) :
    highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun u => highUnionSourceDensity C R h (x u))
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) ((highUnionSourceState C R h).2 j) y =
      completeSourceRawNumerator (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) lam ℓ N μ D M q Cfr a V η U
        (fun u => highUnionSourceDensity C R h (x u)) g w ((highUnionSourceState C R h).2 j) y := by
  unfold highMarkedLocalScoreNumerator completeSourceRawNumerator
  rw [completeSourceResponseAction_eq_signed_first_action C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN j h x hx a V η ha g w hp y]
  rfl

end
end NearlyMinimax
