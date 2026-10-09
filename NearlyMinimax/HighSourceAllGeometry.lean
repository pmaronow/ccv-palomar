module

public import NearlyMinimax.HighSourceOriginalGeometry


@[expose] public section

/-! Uniform, actual canonical-source domination by the full-count geometry
H. No hypothesis asserts score boundedness or a stochastic covariance. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

 theorem completeSource_original_all_geometry {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 2 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
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
      ∀ n : ℕ, ∀ x : Fin n → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      let eta := cf*(k : ℝ)^(-C.smoothness)
      let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
        completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta
          Chi (highRowTotalMass R.rowMass) n (highPatchProductChart d k j x) := by
  obtain ⟨CG,eG,hCG,heG,hguards⟩ := completeSource_original_local_guards C Q
  obtain ⟨CR,eR,hCR,heR,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
  obtain ⟨CP,eP,hCP,heP,hpair⟩ := completeSource_original_count_two C Q
  obtain ⟨CH,eH,hCH,heH,hhigher⟩ := completeSource_original_higher_geometry C Q
  obtain ⟨CB,eB,hCB,heB,hcrude⟩ := completeSourceNumerator_original_field_bound C Q
  let C0 := max (max CG CR) (max CP (max CH CB))
  let e0 := min (min eG eR) (min eP (min eH eB))
  have hG0 : CG ≤ C0 := (le_max_left _ _).trans (le_max_left _ _)
  have hR0 : CR ≤ C0 := (le_max_right _ _).trans (le_max_left _ _)
  have hP0 : CP ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
  have hH0 : CH ≤ C0 := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hB0 : CB ≤ C0 := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have heG0 : e0 ≤ eG := (min_le_left _ _).trans (min_le_left _ _)
  have heR0 : e0 ≤ eR := (min_le_left _ _).trans (min_le_right _ _)
  have heP0 : e0 ≤ eP := (min_le_right _ _).trans (min_le_left _ _)
  have heH0 : e0 ≤ eH := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heB0 : e0 ≤ eB := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨C0,e0,hCG.trans hG0,lt_min (lt_min heG heR) (lt_min heP (lt_min heH heB)),?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
    Rbound hI V hV j h n x hx
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
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  have hellp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hfr1 := hCG.trans (hG0.trans hfr)
  have H := hguards k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
    (hG0.trans hfr) hellp hellN hcf (heta.trans heG0) h
  have G := completeSourceRows_guards C k D M q hD (by omega) hM Cfr lam ell N mu hfr1 hellp hellN
  change selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
    completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta
      Chi (highRowTotalMass R.rowMass) n U
  rcases n with _|_|_|n
  · have hz (y : Fin 0 → Fin 3) := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
      (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 0 x hx y).2 (by omega)
    change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 0 Q.a V eta h j) x ≤ 0
    simp only [selectedRawSquareEnergy]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    change highUnionSourceMarkedNumerator C R 0 Q.a V eta j h x y^2 = 0
    rw [hz, zero_pow (by decide : 2 ≠ 0)]
  · have hz (y : Fin 1 → Fin 3) := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
      (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 1 x hx y).2 (by omega)
    change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 1 Q.a V eta h j) x ≤ 0
    simp only [selectedRawSquareEnergy]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    change highUnionSourceMarkedNumerator C R 1 Q.a V eta j h x y^2 = 0
    rw [hz, zero_pow (by decide : 2 ≠ 0)]
  · obtain ⟨had,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
    have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards C (M : ℝ) hM).1
    have hpi (i : Fin 2) : p i ∈ Icc (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) :=
      highUnionSourceDensity_interval C R G h (x i)
    have hUi (i : Fin 2) : U i ∈ hyperplaneCube d := highLocalCoordinates_abs_le_one d k j (x i)
    have hf (i : Fin 2) : |coefficientRegression eta g w (fun i => highFrameFeature (U i)) (c j) i| ≤ Q.ρ :=
      H.regression_abs j (c j) (H.coefficient_ball j) (x i)
    have he (y : Fin 2 → Fin 3) : highUnionSourceRawNumerator C R 2 Q.a V eta h j x y =
        finePairCountTwoRawNumerator (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) ell N D M q
          Cfr Q.a V eta U p g w (c j) y := by
      have hp := hpair k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf
        (hP0.trans hfr) hellp hellN hcf (heta.trans heP0) V hV j h x hx y
      have hfine := finePairThreeRow_count_two_numerator hD _ _ ell N had hab hellp.le hellN.le
        D M q (by omega) hM2 hq Cfr Q.a V eta (by linarith) U hUi p hpi g w (c j) y
      change highUnionSourceRawNumerator C R 2 Q.a V eta h j x y = _ at hp
      exact hp.trans hfine.symm
    have hcap := finePairCountTwoRawNumerator_sum_square_le_geometry hD _ _ ell N had hab hellp.le hellN.le
      D M q (by omega) hM2 hq Cfr Q.a V eta Q.ρ (by linarith) Q.a_pos Q.ρ_pos.le U hUi
      p g w hpi (fun i => H.weight_abs j (x i)) (c j) hf
    change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 2 Q.a V eta h j) x ≤
      finePairCountTwoGeometryEnvelope (C.densityUpper-(M : ℝ)⁻¹) Q.a Q.ρ eta N U
    have hs : selectedRawSquareEnergy (highUnionSourceRawNumerator C R 2 Q.a V eta h j) x =
        ∑ y : Fin 2 → Fin 3, finePairCountTwoRawNumerator (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) ell N D M q Cfr Q.a V eta U p g w (c j) y^2 := by
      unfold selectedRawSquareEnergy
      apply Finset.sum_congr (by ext y; simp)
      intro y _
      rw [he]
    exact hs.trans_le (by simpa only [one_div] using hcap)
  · by_cases hnD : n+3 ≤ D
    · change selectedRawSquareEnergy (highUnionSourceRawNumerator C R (n+3) Q.a V eta h j) x ≤
        if n+3 ≤ D then completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
          M Rbound q Cfr Q.a Q.ρ eta U else (3*Chi^2)^(n+3)*eta^4*(highRowTotalMass R.rowMass+1)^2
      rw [if_pos hnD]
      exact hhigher k D M q hk0 horder hk hD (by omega) hM Cfr c0 ell N mu cf
        (hH0.trans hfr) hell hellN hcf (heta.trans heH0) htau hnu hFine Rbound hI V hV j h (n+3) (by omega) hnD x hx
    · change selectedRawSquareEnergy (highUnionSourceRawNumerator C R (n+3) Q.a V eta h j) x ≤
        if n+3 ≤ D then completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
          M Rbound q Cfr Q.a Q.ρ eta U else (3*Chi^2)^(n+3)*eta^4*(highRowTotalMass R.rowMass+1)^2
      rw [if_neg hnD]
      apply crude_raw_square_energy_pointwise Chi eta (highRowTotalMass R.rowMass)
      · exact (highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1).le
      · exact G.total_positive.le
      · intro z y
        exact hcrude k D M q (n+3) hk0 horder hk hD (by omega) (by omega) hM Cfr lam ell N mu cf
          (hB0.trans hfr) hellp hellN hcf (heta.trans heB0) V hV j h z y

end NearlyMinimax
