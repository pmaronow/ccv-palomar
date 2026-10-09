module

public import NearlyMinimax.PaperLowerRegimeAliasInfiniteTail
public import NearlyMinimax.HighSourceFinalDecomposition


@[expose] public section

/-! The literal alias norm acts on the same actual signed source component
as the full update's exact count decomposition, uniformly for every Reg(K). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem paperRegimeAliasRawAction_eq_actual_aliases {d n F : ℕ}
    (C : ModelConstants d) (K Cfr a : ℝ) (M D q : ℕ) (N mu eta : ℝ)
    (hn : 3 ≤ n) (hres : highCenterResolutionThreshold C ≤ (M : ℝ))
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (z : LocalNuisance (HighFrameIndex d F) n) (U : Fin n → Covariate d)
    (y : Fin n → Fin 3) :
    let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
    let ell := N*Real.exp (-c0*(D : ℝ))
    let ad := C.densityLower+(M : ℝ)⁻¹
    let bd := C.densityUpper-(M : ℝ)⁻¹
    paperRegimeAliasRawAction C K Cfr a M D q N mu eta w z U y =
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ell N mu)
        ad bd (spatialInterpolationLambda d) ell (fun r => higherBandTargetScale d r N mu)
        M q Cfr a z.2.2.2 eta U z.1 z.2.2.1 (w U) z.2.1 y else 0) +
      finePairPairAliasAction ad bd ell N M q Cfr U z.1 z.2.1
        (fun v => highResponseProduct a z.2.2.2 eta z.2.2.1 (w U)
          (fun i => highFrameFeature (U i)) v y) := by
  obtain ⟨had,hab⟩ := high_source_interval_numeric C (M : ℝ) hres
  have had' : 0 < C.densityLower+(M : ℝ)⁻¹ := by simpa only [one_div] using had
  have hab' : C.densityLower+(M : ℝ)⁻¹ < C.densityUpper-(M : ℝ)⁻¹ := by
    simpa only [one_div] using hab
  dsimp only
  by_cases hc : M<n
  · simp only [paperRegimeAliasRawAction,if_pos hc]
  · have hp := finePairPairAliasAction_zero_selected_count
      (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹)
      (N*Real.exp (-(densityIntervalExponent C.densityLower C.densityUpper+1)*(D : ℝ)))
      N had' hab' M q hn
      (by omega : n ≤ M) Cfr U z.1 z.2.1
      (fun v => highResponseProduct a z.2.2.2 eta z.2.2.1 (w U)
        (fun i => highFrameFeature (U i)) v y)
    simp only [paperRegimeAliasRawAction,if_neg hc,zero_add]
    exact hp.symm

theorem paperRegimeAliasRawAction_zero_through_resolution {d n F : ℕ}
    (C : ModelConstants d) (K Cfr a : ℝ) (M D q : ℕ) (N mu eta : ℝ)
    (hn : n ≤ M) (w : (Fin n → Covariate d) → Fin n → ℝ)
    (z : LocalNuisance (HighFrameIndex d F) n) (U : Fin n → Covariate d)
    (y : Fin n → Fin 3) :
    paperRegimeAliasRawAction C K Cfr a M D q N mu eta w z U y = 0 := by
  simp only [paperRegimeAliasRawAction,if_neg (not_lt.mpr hn)]

theorem paperLowerRegime_uniform_source_decomposition {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr : ℝ) (hK : 1 ≤ K) (hCfr : 1 ≤ Cfr) (q : ℕ) (hq : 1 ≤ q) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ n : ℕ, 3 ≤ n → n ≤ D →
      ∀ (w : (Fin n → Covariate d) → Fin n → ℝ)
      (z : LocalNuisance (HighFrameIndex d D) n)
      (U : Fin n → Covariate d) (y : Fin n → Fin 3),
      (∀ i l, |U i l| ≤ 2) →
      z ∈ localNuisanceSet (HighFrameIndex d D) n
        (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) Cfr Q.ρ Q.v →
      let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
      let ell := N*Real.exp (-c0*(D : ℝ))
      let ad := C.densityLower+(M : ℝ)⁻¹
      let bd := C.densityUpper-(M : ℝ)⁻¹
      completeSourceRawNumerator ad bd (spatialInterpolationLambda d) ell N mu D M q Cfr Q.a z.2.2.2 eta
        U z.1 z.2.2.1 (w U) z.2.1 y =
      eta^2*(∏ i, z.1 i)*∑ i, (w U i)^2*
        (integratedCardinalWeight (spatialInterpolationLambda d) (higherBandTargetScale d n N mu) U i-1)*
        highResponseVarianceTerm Q.a z.2.2.2 eta z.2.2.1 (w U) (fun i => highFrameFeature (U i)) z.2.1 y i +
      (∏ i, z.1 i)*highResponseDefect q Cfr Q.a z.2.2.2 eta
        (integratedCardinalMatrix (spatialInterpolationLambda d) (higherBandTargetScale d n N mu) U)
        z.2.2.1 (w U) (fun i => highFrameFeature (U i)) z.2.1 y +
      paperRegimeAliasRawAction C K Cfr Q.a M D q N mu eta w z U y +
      finePairEvenFieldAction ad bd ell N M q Cfr U z.1 z.2.1
        (fun v => highResponseProduct Q.a z.2.2.2 eta z.2.2.1 (w U)
          (fun i => highFrameFeature (U i)) v y) := by
  have hd : 0<d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hab : C.densityLower<C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_hierarchy hd C Q K c0 1 1 hK hc0 (by norm_num) (by norm_num)
  let M0 := max M1 (Nat.ceil (highCenterResolutionThreshold C))
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R n hn hnD w z U y hU hz
  have hres : highCenterResolutionThreshold C ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hm))
  have H := hM1 M D ((le_max_left _ _).trans hm) N mu eta R
  obtain ⟨had,hint⟩ := high_source_interval_numeric C (M : ℝ) hres
  have had' : 0<C.densityLower+(M : ℝ)⁻¹ := by simpa only [one_div] using had
  have hint' : C.densityLower+(M : ℝ)⁻¹<C.densityUpper-(M : ℝ)⁻¹ := by simpa only [one_div] using hint
  have hN : 0<N := lt_of_lt_of_le zero_lt_one R.scale
  have hnu (j : Fin (D-2)) : 0<higherBandTargetScale d (j.val+3) N mu := by
    unfold higherBandTargetScale
    exact mul_pos hN (Real.rpow_pos_of_pos (mul_pos R.occupancy_positive R.H_positive) _)
  have hfine (j : Fin (D-2)) (hj : N*Real.exp (-c0*D)<higherBandTargetScale d (j.val+3) N mu) :
      j.val+3≤M := (H.target_count _ hj).trans H.target_resolution
  have hpD := (localNuisanceSet_guards (HighFrameIndex d D) n _ _ Cfr Q.ρ Q.v z hz).1
  have he := completeSourceRawNumerator_refined_decomposition
    _ _ (spatialInterpolationLambda d) (N*Real.exp (-c0*D)) N mu had' hint'
    (by unfold spatialInterpolationLambda; positivity) H.cutoff.le D M q hn hnD hnu hfine
    Cfr Q.a z.2.2.2 eta (ne_of_gt (zero_lt_one.trans_le hCfr)) U hU z.1 z.2.2.1 (w U) hpD z.2.1 y
  have ha := paperRegimeAliasRawAction_eq_actual_aliases C K Cfr Q.a M D q N mu eta hn hres w z U y
  dsimp only at ha ⊢
  rw [ha]
  exact he.trans (by ring)

end NearlyMinimax
