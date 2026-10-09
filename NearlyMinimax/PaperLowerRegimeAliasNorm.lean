module

public import NearlyMinimax.PaperLowerRegimeAliasRaw


@[expose] public section

/-! The manuscript's actual compact-nuisance alias norm and its factorial
tail for every Reg(K) tuple, with the constants fixed before the tuple. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def paperRegimeAliasNuisanceEnergy {d n F : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K Cfr : ℝ) (M D q : ℕ) (N mu eta : ℝ)
    (w : (Fin n → Covariate d) → Fin n → ℝ) : (Fin n → Covariate d) → ℝ :=
  compactNuisanceEnergy (localNuisanceSet (HighFrameIndex d F) n
    (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) Cfr Q.ρ Q.v)
    (paperRegimeAliasRawAction C K Cfr Q.a M D q N mu eta w)

theorem PaperLowerRegime.amplitude_half {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) : eta ≤ Q.ρ/2 := by
  have hp : (2 : ℝ) ≤ (2 : ℝ)^(d+1) := by
    calc
      2 = (2 : ℝ)^1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsmall := (le_div_iff₀ (by positivity : 0 < (2 : ℝ)^(d+1))).mp R.amplitude_small
  have hmul := mul_le_mul_of_nonneg_left hp R.amplitude_positive.le
  apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  exact hmul.trans hsmall

theorem paperRegimeAliasNuisanceEnergy_integrable_and_le {d n F : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (K Cfr : ℝ)
    (M D q : ℕ) (N mu eta : ℝ)
    (R : PaperLowerRegime C Q K M D N mu eta)
    (H : PaperRegimeHierarchy d K (densityIntervalExponent C.densityLower C.densityUpper+1) 1 1 M D N mu)
    (hres : highCenterResolutionThreshold C ≤ (M : ℝ))
    (htau : shrunkDensityExponent C.densityLower C.densityUpper M ≤
      densityIntervalExponent C.densityLower C.densityUpper+1)
    (hCfr : 1 ≤ Cfr)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (hw : ∀ i, Measurable (fun U => w U i)) (hwb : ∀ U i, |w U i| ≤ 1)
    (hH : Integrable (paperRegimeAliasGeometryEnvelope C K Cfr Q.a Q.ρ M D q n F N mu eta)
      (fullSpatialPatchDesign d n)) :
    Integrable (paperRegimeAliasNuisanceEnergy (F := F) C Q K Cfr M D q N mu eta w)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, paperRegimeAliasNuisanceEnergy (F := F) C Q K Cfr M D q N mu eta w U
      ∂fullSpatialPatchDesign d n) ≤
    ∫ U, paperRegimeAliasGeometryEnvelope C K Cfr Q.a Q.ρ M D q n F N mu eta U
      ∂fullSpatialPatchDesign d n := by
  obtain ⟨had,hab⟩ := high_source_interval_numeric C (M : ℝ) hres
  have hab' : C.densityLower+(M : ℝ)⁻¹ ≤ C.densityUpper-(M : ℝ)⁻¹ := by
    simpa only [one_div] using hab.le
  let S := localNuisanceSet (HighFrameIndex d F) n
    (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) Cfr Q.ρ Q.v
  have hS : IsCompact S := localNuisanceSet_isCompact _ _ _ _ _ _ _
  have hSn : S.Nonempty := localNuisanceSet_nonempty _ _ hab'
    (zero_le_one.trans hCfr) Q.ρ_pos.le
  apply compactNuisanceEnergy_integrable_and_bound_ae (fullSpatialPatchDesign d n)
    S hS hSn (paperRegimeAliasRawAction C K Cfr Q.a M D q N mu eta w)
    (fun z hz y => paperRegimeAliasRawAction_spatial_measurable C K Cfr Q.a M D q N mu eta
      H.cutoff.le w hw z y)
    (fun U y => (paperRegimeAliasRawAction_continuous_nuisance C K Cfr Q.a M D q N mu eta w U y).continuousOn)
    (paperRegimeAliasGeometryEnvelope C K Cfr Q.a Q.ρ M D q n F N mu eta) hH
  filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube (d := d) (n := n)] with U hU
  intro z hz
  exact paperRegimeAliasRawAction_sum_square_le_geometry C Q K Cfr M D q N mu eta H hres htau
    hCfr R.amplitude_positive.le R.amplitude_half w hwb z hz U
      (fun i l => (hU i l).trans (by norm_num))

theorem paperLowerRegime_uniform_alias_norm_tail {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr Cs : ℝ) (hK : 1 ≤ K) (hCfr : 1 ≤ Cfr) (hCs : 0 ≤ Cs) (q : ℕ) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ (F : ℕ → ℕ)
      (w : ∀ n : ℕ, (Fin n → Covariate d) → Fin n → ℝ),
      (∀ n i, Measurable (fun U => w n U i)) → (∀ n U i, |w n U i| ≤ 1) →
      (∀ n : ℕ, Integrable
        (paperRegimeAliasNuisanceEnergy (F := F n) C Q K Cfr M D q N mu eta (w n))
        (fullSpatialPatchDesign d n)) ∧
      ∀ J : ℕ,
      (∑ j ∈ Finset.range J, poissonCountWeight (Cs*mu) (M+1+j) *
        ∫ U, paperRegimeAliasNuisanceEnergy (F := F (M+1+j)) C Q K Cfr M D q N mu eta (w (M+1+j)) U
          ∂fullSpatialPatchDesign d (M+1+j)) ≤
      paperRegimeAliasFactorialConstant C K Cfr Q.a Q.ρ Cs q *
        (eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*N^(4-(d : ℝ))) *
        poissonCountWeight (paperRegimeAliasFactorialConstant C K Cfr Q.a Q.ρ Cs q*mu) (M+1) := by
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_alias_factorial_tail hd C Q K Cfr Q.a Q.ρ Cs hK hCs q
  have hab : C.densityLower < C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  obtain ⟨M2,hM2⟩ := paperLowerRegime_uniform_hierarchy (by omega : 0<d) C Q K c0 1 1
    hK hc0 (by norm_num) (by norm_num)
  have hevent : ∀ᶠ M : ℕ in atTop, M1 ≤ M ∧ M2 ≤ M ∧
      highCenterResolutionThreshold C ≤ (M : ℝ) ∧
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 := by
    filter_upwards [eventually_ge_atTop M1,eventually_ge_atTop M2,
      eventually_ge_atTop (Nat.ceil (highCenterResolutionThreshold C)),
      shrunkDensityExponent_eventually_le_plus_one C.densityLower_pos hab]
      with M h1 h2 hr ht
    exact ⟨h1,h2,(Nat.le_ceil _).trans (by exact_mod_cast hr),ht⟩
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hevent
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R F w hw hwb
  obtain ⟨h1,h2,hres,htau⟩ := hM0 M hm
  obtain ⟨hi,htail⟩ := hM1 M D h1 N mu eta R F
  have H := hM2 M D h2 N mu eta R
  have hn (n : ℕ) := paperRegimeAliasNuisanceEnergy_integrable_and_le (F := F n)
    C Q K Cfr M D q N mu eta R H hres htau hCfr (w n) (hw n) (hwb n) (hi n)
  refine ⟨fun n => (hn n).1,?_⟩
  intro J
  apply le_trans (Finset.sum_le_sum (fun j hj =>
    mul_le_mul_of_nonneg_left (hn (M+1+j)).2
      (poissonCountWeight_nonneg (mul_nonneg hCs R.occupancy_positive.le) _)))
  exact htail J

end NearlyMinimax
