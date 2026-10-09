module

public import NearlyMinimax.HighCompletePathRisk
public import NearlyMinimax.HighPathBudget


@[expose] public section

/-! The actual complete source gives the manuscript's quantitative local
cost lower bound. The path is constructed from its true activity and
Fisher budget; positivity and variance guards are derived numerically. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable

 theorem highCompleteSource_cost_risk_uniform {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr eta0 ctr : ℝ, 1 ≤ Cfr ∧ 0 < eta0 ∧ 0 < ctr ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ eta0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ n : ℕ, ∀ E : ℝ, 0 ≤ E →
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ cm/(M:ℝ) →
      let Bl := highRowTotalMass R.rowMass/highCenterMix C
      let c := highPathConstant (3^d) Q.ρ eta0
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
        highSourceSpatialSeries d k n C.densityLower Q.c (H t h) ≤ (3^d:ℕ)*(k:ℝ)^d*E) →
      ENNReal.ofReal (ctr*eta^4/(1+Bl^2+(k:ℝ)^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  obtain ⟨Cfr,eta0,hCfr,heta0,hpath⟩ := highCompleteSource_minimax_path_bound_uniform C Q
  let c := highPathConstant (3^d) Q.ρ eta0
  have hc : 0 < c := highPathConstant_pos (3^d) Q.ρ_pos heta0
  let ctr := c^2/(3*(3^d:ℕ)*(2+c)^2)
  have hctr : 0 < ctr := div_pos (sq_pos_of_pos hc) (by positivity)
  refine ⟨Cfr,eta0,ctr,hCfr,heta0,hctr,?_⟩
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
