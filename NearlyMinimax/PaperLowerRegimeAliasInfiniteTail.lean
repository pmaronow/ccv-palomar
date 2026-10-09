module

public import NearlyMinimax.PaperLowerRegimeAliasNorm


@[expose] public section

/-! The actual infinite alias factorial series from the manuscript,
including summability, for every tuple in Reg(K). -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem paperRegimeAliasNuisanceEnergy_nonneg {d n F : ℕ}
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (K Cfr : ℝ)
    (M D q : ℕ) (N mu eta : ℝ)
    (hres : highCenterResolutionThreshold C ≤ (M : ℝ)) (hCfr : 1 ≤ Cfr)
    (w : (Fin n → Covariate d) → Fin n → ℝ) (U : Fin n → Covariate d) :
    0 ≤ paperRegimeAliasNuisanceEnergy (F := F) C Q K Cfr M D q N mu eta w U := by
  obtain ⟨had,hab⟩ := high_source_interval_numeric C (M : ℝ) hres
  have hab' : C.densityLower+(M : ℝ)⁻¹ ≤ C.densityUpper-(M : ℝ)⁻¹ := by
    simpa only [one_div] using hab.le
  exact compactNuisanceEnergy_nonneg _
    (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (localNuisanceSet_nonempty _ _ hab' (zero_le_one.trans hCfr) Q.ρ_pos.le)
    _ (fun U y => (paperRegimeAliasRawAction_continuous_nuisance C K Cfr Q.a M D q N mu eta w U y).continuousOn) U

theorem paperLowerRegime_uniform_alias_norm_infinite_tail {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr Cs : ℝ) (hK : 1 ≤ K) (hCfr : 1 ≤ Cfr) (hCs : 0 ≤ Cs) (q : ℕ) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ (F : ℕ → ℕ)
      (w : ∀ n : ℕ, (Fin n → Covariate d) → Fin n → ℝ),
      (∀ n i, Measurable (fun U => w n U i)) → (∀ n U i, |w n U i| ≤ 1) →
      (∀ n : ℕ, Integrable
        (paperRegimeAliasNuisanceEnergy (F := F n) C Q K Cfr M D q N mu eta (w n))
        (fullSpatialPatchDesign d n)) ∧
      Summable (fun j : ℕ => poissonCountWeight (Cs*mu) (M+1+j) *
        ∫ U, paperRegimeAliasNuisanceEnergy (F := F (M+1+j)) C Q K Cfr M D q N mu eta (w (M+1+j)) U
          ∂fullSpatialPatchDesign d (M+1+j)) ∧
      (∑' j : ℕ, poissonCountWeight (Cs*mu) (M+1+j) *
        ∫ U, paperRegimeAliasNuisanceEnergy (F := F (M+1+j)) C Q K Cfr M D q N mu eta (w (M+1+j)) U
          ∂fullSpatialPatchDesign d (M+1+j)) ≤
      paperRegimeAliasFactorialConstant C K Cfr Q.a Q.ρ Cs q *
        (eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*N^(4-(d : ℝ))) *
        poissonCountWeight (paperRegimeAliasFactorialConstant C K Cfr Q.a Q.ρ Cs q*mu) (M+1) := by
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_alias_norm_tail hd C Q K Cfr Cs hK hCfr hCs q
  let M0 := max M1 (Nat.ceil (highCenterResolutionThreshold C))
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R F w hw hwb
  have hm1 : M1 ≤ M := (le_max_left _ _).trans hm
  have hres : highCenterResolutionThreshold C ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hm))
  obtain ⟨hi,htail⟩ := hM1 M D hm1 N mu eta R F w hw hwb
  have hnonneg (j : ℕ) : 0 ≤ poissonCountWeight (Cs*mu) (M+1+j) *
      ∫ U, paperRegimeAliasNuisanceEnergy (F := F (M+1+j)) C Q K Cfr M D q N mu eta (w (M+1+j)) U
        ∂fullSpatialPatchDesign d (M+1+j) := by
    apply mul_nonneg (poissonCountWeight_nonneg (mul_nonneg hCs R.occupancy_positive.le) _)
    apply integral_nonneg
    exact paperRegimeAliasNuisanceEnergy_nonneg C Q K Cfr M D q N mu eta hres hCfr (w (M+1+j))
  exact ⟨hi,summable_of_sum_range_le hnonneg htail,Real.tsum_le_of_sum_range_le hnonneg htail⟩

end NearlyMinimax
