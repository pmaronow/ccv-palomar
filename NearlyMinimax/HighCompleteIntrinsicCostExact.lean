module

public import NearlyMinimax.HighCompleteCostRisk
public import NearlyMinimax.SourceIntrinsicScoreLegality
public import NearlyMinimax.HighUnionRawFisherExact


@[expose] public section

/-! Exact chart path and cost bounds with the literal intrinsic frame and
source amplitude cap. The envelopes in this intermediate theorem are replaced
by the actual compact-nuisance energy in PaperScoreRisk. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel

/-- All constants imposing model legality and the response floor are fixed
before the extension domain and every statistical parameter. The only energy
inputs are genuine raw local numerator envelopes and their factorial sum. -/
theorem highCompleteSource_intrinsic_minimax_path_bound_exact {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q (highIntrinsicFrameConstant C) lam ell N mu
      let Ω := HighCompleteSourceHistory C k D M q (highIntrinsicFrameConstant C) lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ (Q.ρ/(2:ℝ)^(d+1)) →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ n : ℕ, ∀ T B : ℝ, ∀ hT : 0 ≤ T, 0 ≤ B →
      T*(highRowTotalMass R.rowMass/highCenterMix C)/historyReferenceRho (3^d) ≤
        1/(2+8*((3^d:ℕ):ℝ)^2) →
      eta^2*T ≤ Q.ρ →
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ cm/(M:ℝ) →
      ∀ H : ℝ → Ω → HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ,
      (∀ t ∈ Icc 0 T, ∀ h j r, Integrable (H t h j r)
        (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)))) →
      (∀ t ∈ Icc 0 T, ∀ h j r u, 0 ≤ H t h j r u) →
      (∀ t ∈ Icc 0 T, ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v-eta^2*t) eta h j) x ≤
          H t h j r (highPatchProductChart d k j x)) →
      (∀ t ∈ Icc 0 T, ∀ h, highSourceSpatialSeriesExact d k n C.densityLower Q.c (H t h) ≤ B) →
      ENNReal.ofReal (eta^4*T^2/(2+T*Real.sqrt B)^2-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  let Cfr := highIntrinsicFrameConstant C
  let eta0 := Q.ρ/(2:ℝ)^(d+1)
  have hCfr : 1 ≤ Cfr := highIntrinsicFrameConstant_ge_one C
  have heta0 : 0 < eta0 := div_pos Q.ρ_pos (by positivity)
  have hmodel := highUnionSource_intrinsic_original_model_uniform C Q
  have hfloor := highUnionSource_intrinsic_ternary_floor C Q
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
  let E := SourceRowMark d D M q (C.densityLower+1/(M:ℝ)) (C.densityUpper-1/(M:ℝ)) Cfr lam ell N mu
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  have hpos := completeSourceRows_mass_positive (k := k) C hD hq hM Cfr lam ell N mu hCfr hell hellN
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  dsimp only
  intro cf hcf hcfH
  let eta := cf*(k : ℝ)^(-C.smoothness)
  intro heta cm hcm hcmU n T B hT hB hsmall hVbudget heps H hH hH0 hdom hbudget
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R eta
  have hp : Measurable (Function.uncurry p) := highUnionSourceDensity_joint_measurable C R G
  have hF : Measurable (Function.uncurry F) := highUnionSourceRegression_joint_measurable C R G eta
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let Ba := highRowTotalMass R.rowMass/highCenterMix C
  let ν (t : ℝ) := historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t π act
  have hBa : 0 ≤ Ba := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hν (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (ν t) :=
    completeSourcePrior_probability C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht
  have hV (t : ℝ) (ht : t ∈ Icc 0 T) : |(Q.v-eta^2*t)-Q.v| ≤ Q.ρ := by
    simp only [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg eta),abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hVbudget
  have hqFloor (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3) :
      Q.c ≤ ternaryMass Q.a (F h x) (Q.v-eta^2*t) y :=
    hfloor k D hk0 horder hk _ inferInstance E inferInstance R (M:ℝ)
      G cf hcf heta h _ (hV t ht) x y
  have hqPos (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3) :
      0 < ternaryMass Q.a (F h x) (Q.v-eta^2*t) y := Q.c_pos.trans_le (hqFloor t ht h x y)
  have hqNonneg := fun t ht h x y => (hqPos t ht h x y).le
  let θ := highNormalizedParameterPath T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg
  let bad : ℝ → Set Ω := fun _ => {h | cm/(M:ℝ) < |highUnionSourceMass C R h-1|}
  let eps := 2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper))
  have hm : Measurable (highUnionSourceMass C R) := highUnionSourceMass_measurable C R G
  have hbad (t : ℝ) (_ : t ∈ Icc 0 T) : MeasurableSet (bad t) :=
    measurableSet_lt measurable_const ((hm.sub_const 1).abs)
  have hlegal (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (hh : h ∉ bad t) :
      Admissible (C.withDomain U) (θ t h) := by
    have hgood : |highUnionSourceMass C R h-1| ≤ cm/(M:ℝ) := le_of_not_gt hh
    obtain ⟨_,hlegal⟩ := hmodel U k D hk0 horder hk _ inferInstance E inferInstance inferInstance
      R (M:ℝ) G cf hcf hcfH heta cm hcm hcmU h hgood _ (hV t ht)
    change Admissible (C.withDomain U)
      (highNormalizedParameterPath T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t h)
    rw [highNormalizedParameterPath_apply T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h]
    exact hlegal
  have hmassEq : (fun h => highRawDensityMass (p h)) = highUnionSourceMass C R := by
    funext h
    simp only [p,highRawDensityMass,highUnionSourceMass]
  have hmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      Measure.map (fun h => highRawDensityMass (p h)) (ν t) =
      Measure.map (fun h => highRawDensityMass (p h)) (ν 0) := by
    have h1 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht
    have h0 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall 0 ⟨le_rfl,hT⟩
    rw [hmassEq]
    exact h1.trans h0.symm
  have hbadmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      (massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n).real (bad t) ≤ eps := by
    rw [hmassEq]
    exact completeSourceMass_prior_tilted_tail C hD hq hM Cfr lam ell N mu hCfr hell hellN
      (by omega) T hT hsmall n (cm/(M:ℝ)) heps t ht
  have hfisher (t : ℝ) (ht : t ∈ Icc 0 T) := by
    letI := hν t ht
    exact highUnionSource_raw_fisher_bound_exact C R G hpos (ν t) n hk Q.a (Q.v-eta^2*t) eta Q.c
      Q.a_pos.ne' Q.c_pos (hqFloor t ht)
      (fun j h x => completeSourceDensity_product_zero C hD hq hM Cfr lam ell N mu hCfr hell hellN j h n x)
      (H t) (hH t ht) (hH0 t ht) (hdom t ht) B hB (hbudget t ht)
  have hactm := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  have hact := highUnionSourceActivation_centered C R G hpos
  have hab := highUnionSourceActivation_bound C R G hpos
  have hh := historyMarkedPrior_original_minimax_path_bound
    (fun i j => j ∈ highNeighborLabels d k i) (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    π act hactm hact Ba T hBa hT hab hsmall (C.withDomain U) n Q.a Q.v eta
    C.densityLower C.densityUpper B eps Q.a_pos C.densityLower_pos p F hp hF
    (highUnionSourceDensity_coarse_interval C R G) hqPos hmass θ
    (fun t ht h => highNormalizedParameterPath_apply T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h)
    (fun t ht => Q.effective_interval (hV t ht)) bad hbad hlegal hbadmass
    (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
  let P (t : ℝ) := (highRealSampleKernel n Q.a (Q.v-eta^2*t) p F hp hF) ∘ₘ
    massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n
  let Score (t : ℝ) := highMarginalRealScore (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (ν t) π act n Q.a (Q.v-eta^2*t) eta p F
  letI := historyMarkedReference_probability (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)) (highNeighbor_dependency_card d k) π
  have hInt := highHistoryScore_sqrt_energy_intervalIntegrable
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d) π act hactm
    Ba hBa hab n Q.a Q.v eta C.densityLower C.densityUpper T B Q.a_pos C.densityLower_pos
    hT p F hp hF hν (highUnionSourceDensity_coarse_interval C R G) hqPos
    (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
  have henergy (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ z, (Score t z)^2 ∂P t) ≤ B := by
    letI := hν t ht
    exact ((highMarginalRealScore_memLp_energy _ _ (ν t) π act hactm Ba hBa hab n Q.a
      (Q.v-eta^2*t) eta C.densityLower C.densityUpper Q.a_pos C.densityLower_pos
      p F hp hF (highUnionSourceDensity_coarse_interval C R G) (hqPos t ht)
      (hfisher t ht).1).2).trans (hfisher t ht).2
  have hscore := intervalIntegral_sqrt_energy_le
    (fun t => ∫ z, (Score t z)^2 ∂P t) T B hT hInt henergy
  have hsc0 : 0 ≤ ∫ t in (0:ℝ)..T, Real.sqrt (∫ z, (Score t z)^2 ∂P t) :=
    intervalIntegral.integral_nonneg hT (fun _ _ => Real.sqrt_nonneg _)
  have hfrac : eta^4*T^2/(2+T*Real.sqrt B)^2 ≤
      eta^4*T^2/(2+∫ t in (0:ℝ)..T, Real.sqrt (∫ z, (Score t z)^2 ∂P t))^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact (sq_le_sq₀ (by linarith) (by positivity)).mpr (by linarith)
  have hout := (ENNReal.ofReal_le_ofReal (sub_le_sub_right hfrac _)).trans hh
  simpa only [ModelConstants.withDomain,effectiveVarianceUpper] using hout


 theorem highCompleteSource_intrinsic_cost_risk_exact {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
      ∃ ctr : ℝ, 0 < ctr ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q (highIntrinsicFrameConstant C) lam ell N mu
      let Ω := HighCompleteSourceHistory C k D M q (highIntrinsicFrameConstant C) lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ (Q.ρ/(2:ℝ)^(d+1)) →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ n : ℕ, ∀ E : ℝ, 0 ≤ E →
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ cm/(M:ℝ) →
      let Bl := highRowTotalMass R.rowMass/highCenterMix C
      let c := highPathConstant (3^d) Q.ρ (Q.ρ/(2:ℝ)^(d+1))
      let I := Real.sqrt ((3^d:ℕ)*(k:ℝ)^d*E)
      let delta := localScorePathLength c Bl I
      ∀ H : ℝ → Ω → HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ,
      (∀ t ∈ Icc 0 delta, ∀ h j r, Integrable (H t h j r)
        (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)))) →
      (∀ t ∈ Icc 0 delta, ∀ h j r u, 0 ≤ H t h j r u) →
      (∀ t ∈ Icc 0 delta, ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v-eta^2*t) eta h j) x ≤
          H t h j r (highPatchProductChart d k j x)) →
      (∀ t ∈ Icc 0 delta, ∀ h,
        highSourceSpatialSeriesExact d k n C.densityLower Q.c (H t h) ≤ (3^d:ℕ)*(k:ℝ)^d*E) →
      ENNReal.ofReal (ctr*eta^4/(1+Bl^2+(k:ℝ)^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  let Cfr := highIntrinsicFrameConstant C
  let eta0 := Q.ρ/(2:ℝ)^(d+1)
  have hCfr : 1 ≤ Cfr := highIntrinsicFrameConstant_ge_one C
  have heta0 : 0 < eta0 := div_pos Q.ρ_pos (by positivity)
  have hpath := highCompleteSource_intrinsic_minimax_path_bound_exact C Q
  let c := highPathConstant (3^d) Q.ρ eta0
  have hc : 0 < c := highPathConstant_pos (3^d) Q.ρ_pos heta0
  let ctr := c^2/(3*(3^d:ℕ)*(2+c)^2)
  have hctr : 0 < ctr := div_pos (sq_pos_of_pos hc) (by positivity)
  refine ⟨ctr,hctr,?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  dsimp only
  intro cf hcf hcfH heta cm hcm hcmU n E hE heps H hH hH0 hdom hbudget
  let eta := cf*(k:ℝ)^(-C.smoothness)
  let Bl := highRowTotalMass R.rowMass/highCenterMix C
  let I := Real.sqrt ((3^d:ℕ)*(k:ℝ)^d*E)
  let delta := localScorePathLength c Bl I
  have hBl : 0 ≤ Bl := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hI : 0 ≤ I := Real.sqrt_nonneg _
  have hdelt : 0 < delta := localScorePathLength_pos hc hBl hI
  have hnumE : 0 ≤ (k:ℝ)^d*E := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hE
  have hbudget0 : 0 ≤ (3^d:ℕ)*(k:ℝ)^d*E := by positivity
  have hsmall := highPath_update_budget (3^d) Q.ρ_pos heta0 hBl hI
  have heta0' : 0 ≤ eta := mul_nonneg hcf (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hV := highPath_variance_budget (3^d) Q.ρ_pos heta0 hBl hI heta0' heta
  have hh := hpath U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
    cf hcf hcfH heta cm hcm hcmU n delta ((3^d:ℕ)*(k:ℝ)^d*E) hdelt.le hbudget0
    hsmall hV heps H hH hH0 hdom hbudget
  have hIE : I^2 = (3^d:ℕ)*((k:ℝ)^d*E) := by
    simpa only [I,mul_assoc] using Real.sq_sqrt hbudget0
  have hK : (1:ℝ) ≤ (3^d:ℕ) := by exact_mod_cast one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)
  have hn := score_cost_scaled_numeric (eta := eta) hc hBl hI (mul_nonneg hdelt.le hI)
    (show delta*I ≤ localScorePathLength c Bl I*I from le_rfl) hK hnumE hIE
  have hout := (ENNReal.ofReal_le_ofReal (sub_le_sub_right hn _)).trans hh
  exact hout


end NearlyMinimax
