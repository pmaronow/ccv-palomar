module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.HighSourceOriginalPair
public import NearlyMinimax.HighUnionFisher


@[expose] public section

/-! The higher-count universal geometry envelope dominates the actual
canonical complete source in the original periodic-frame model. Response
and coefficient legality are derived, rather than supplied as assumptions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

 theorem completeSource_original_higher_geometry {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 1 ≤ ell → ell < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 →
      (∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu) →
      (∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) →
      ∀ Rbound : ℕ, (∀ r ∈ ordinaryFineAliasTargetSet d D ell N mu, 1 ≤ r ∧ r ≤ Rbound) →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr (spatialInterpolationLambda d) ell N mu)),
      ∀ n : ℕ, 3 ≤ n → n ≤ D → ∀ x : Fin n → Covariate d,
      (∀ i, x i ∈ highTorusPatch d k j) →
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      let eta := cf*(k : ℝ)^(-C.smoothness)
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
        completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
          M Rbound q Cfr Q.a Q.ρ eta (highPatchProductChart d k j x) := by
  obtain ⟨CfrG,etaG,hfrG,hetaG,hguards⟩ := completeSource_original_local_guards C Q
  obtain ⟨CfrR,etaR,hfrR,hetaR,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
  refine ⟨max CfrG CfrR, min etaG etaR, hfrG.trans (le_max_left _ _), lt_min hetaG hetaR,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
    Rbound hI V hV j h n hn hnD x hx
  letI := hk0
  letI := horder
  let lam := spatialInterpolationLambda d
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf*(k : ℝ)^(-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let U := highPatchProductChart d k j x
  let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
  let g := fun i : Fin n => highLocalFieldWithout d k D eta c j (x i)
  let w := fun i : Fin n => highPeriodicTensor d k j (x i)
  have hfrg := (le_max_left CfrG CfrR).trans hfr
  have hfrr := (le_max_right CfrG CfrR).trans hfr
  have hfr1 := hfrG.trans hfrg
  have heG := heta.trans (min_le_left _ _)
  have heR := heta.trans (min_le_right _ _)
  have hellp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have H := hguards k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfrg hellp hellN hcf heG h
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hfr1 hellp hellN
  obtain ⟨had,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hUi (i : Fin n) (l : Fin d) : |U i l| ≤ 2 :=
    (highLocalCoordinates_abs_le_one d k j (x i) l).trans (by norm_num)
  have hpi (i : Fin n) : p i ∈ Icc (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) :=
    highUnionSourceDensity_interval C R G h (x i)
  have hp (f : ℝ) (hf : |f| ≤ Q.ρ) (u : Fin 3) : 0 ≤ ternaryMass Q.a f V u :=
    Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 u)
  have hcap := completeSourceRawNumerator_higher_square_le_geometry C.densityLower C.densityUpper c0 ell N mu
    C.densityLower_pos hell D M Rbound q (by simpa only [one_div] using hab) htau hn hnD hq hnu hFine hI Cfr Q.a V eta Q.ρ
    hfr1 Q.a_pos H.amplitude_nonneg Q.ρ_pos.le H.amplitude_half U hUi p g w (by simpa only [one_div] using hpi)
    (fun i => H.without_abs j (x i)) (fun i => H.weight_abs j (x i)) (c j) (H.coefficient_ball j) hp
  have he (y : Fin n → Fin 3) : highUnionSourceRawNumerator C R n Q.a V eta h j x y =
      completeSourceRawNumerator (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) lam ell N mu
        D M q Cfr Q.a V eta U p g w (c j) y :=
    (hresponse k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfrr hellp hellN hcf heR
      V hV j h n x hx y).1
  have hs : selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x =
      ∑ y : Fin n → Fin 3, completeSourceRawNumerator (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y^2 := by
    unfold selectedRawSquareEnergy
    apply Finset.sum_congr (by ext y; simp)
    intro y _
    rw [he]
  change selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
    completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu M Rbound q Cfr Q.a Q.ρ eta U
  exact hs.trans_le (by simpa only [one_div] using hcap)

end NearlyMinimax
