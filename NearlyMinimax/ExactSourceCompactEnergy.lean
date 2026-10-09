module

public import NearlyMinimax.HighSourceNuisanceNorm
public import NearlyMinimax.HighSourceAffineTail
public import NearlyMinimax.HighCompleteSourceMarkedTail
public import NearlyMinimax.PoissonEnergyBounds


@[expose] public section

/-! The exact manuscript local energy, with its actual compact nuisance
supremum before spatial integration. Generic full-response bounds prove
finiteness without a numerical-regime or supplied energy hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

def exactSourceCompactEnvelope {d D M q : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr lam ell N mu eta : ℝ)
    (r : ℕ) (U : Fin r → Covariate d) : ℝ :=
  compactNuisanceEnergy
    (localNuisanceSet (HighFrameIndex d D) r
      (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v)
    (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta) U

def exactSourceLiteralEnergy {d D M q : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr lam ell N mu eta x : ℝ) : ℝ :=
  ∑' r : ℕ, poissonCountWeight x r *
    completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r)
      C Cfr lam ell N mu Q eta

section Actual
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ell N mu : ℝ) (hCfr : 1 ≤ Cfr) (hell : 0 < ell) (hellN : ell < N)
  (Q : LowSmoothnessTernaryConstants C) (eta : ℝ) (hk : 4 ≤ k)
  (heta : 0 ≤ eta) (hetaQ : eta ≤ Q.ρ/2)
set_option quotPrecheck false
local notation "R" => completeSourceRows C k D M q Cfr lam ell N mu
local notation "Chi" => highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
local notation "B" => highRowTotalMass (R).rowMass
local notation "H" => exactSourceCompactEnvelope (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta
include hD hq hM hCfr hell hellN hk heta hetaQ

theorem exactSourcePatchNumerator_abs_bound (r : ℕ)
    (z : LocalNuisance (HighFrameIndex d D) r)
    (hz : z ∈ localNuisanceSet (HighFrameIndex d D) r
      (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v)
    (U : Fin r → Covariate d) (y : Fin r → Fin 3) :
    |completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta z U y| ≤
      Chi^r*eta^2*(B+1) := by
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  have hChi := highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1
  by_cases hU : U ∈ sourceSpatialPatchSet d r
  · cases r with
    | zero =>
      simp only [completeSourcePatchNumerator, if_pos hU]
      rw [completeSourceRawNumerator_count_zero _ _ lam ell N mu
        (high_source_interval_numeric C (M : ℝ) hM).1
        (high_source_interval_numeric C (M : ℝ) hM).2 D M q (by omega)]
      simp only [abs_zero]
      positivity [G.total_positive.le]
    | succ r =>
      rw [completeSourcePatchNumerator_eq_marked_inverse C hD hq hM Cfr lam ell N mu
        hCfr hell hellN Q eta hk heta hetaQ (0 : HighWindowLabels d k) z hz U hU y]
      exact completeSourceNuisanceNumerator_all_count_bound C hD hq hM Cfr lam ell N mu
        hCfr hell hellN (by omega) Q eta (by omega) heta hetaQ
        (0 : HighWindowLabels d k) z hz _ y
  · simp only [completeSourcePatchNumerator, if_neg hU, abs_zero]
    positivity [G.total_positive.le]

theorem exactSourceCompactEnvelope_measurable (r : ℕ) : Measurable (H r) :=
  completeSourcePatchEnergy_measurable C hD hq hM Cfr lam ell N mu hCfr hell hellN
    Q eta hk heta hetaQ (0 : HighWindowLabels d k)

theorem exactSourceCompactEnvelope_nonneg (r : ℕ) (U : Fin r → Covariate d) : 0 ≤ H r U := by
  apply compactNuisanceEnergy_nonneg _ (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (localNuisanceSet_nonempty _ _ (high_source_interval_numeric C (M : ℝ) hM).2.le
      (by linarith) Q.ρ_pos.le)
  exact fun W y => completeSourcePatchNumerator_continuousOn C hD hq hM Cfr lam ell N mu
    hCfr hell hellN Q eta hk heta hetaQ (0 : HighWindowLabels d k) W y

theorem exactSourceCompactEnvelope_dominates_legal (r : ℕ)
    (z : LocalNuisance (HighFrameIndex d D) r)
    (hz : z ∈ localNuisanceSet (HighFrameIndex d D) r
      (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v)
    (U : Fin r → Covariate d) :
    (∑ y : Fin r → Fin 3,
      completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta z U y^2) ≤ H r U := by
  obtain ⟨zmax,hzmax,heq,hmax⟩ := compactNuisanceEnergy_attained _
    (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (localNuisanceSet_nonempty _ _ (high_source_interval_numeric C (M : ℝ) hM).2.le
      (by linarith) Q.ρ_pos.le)
    (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta)
    (fun W y => completeSourcePatchNumerator_continuousOn C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaQ (0 : HighWindowLabels d k) W y) U
  change _ ≤ compactNuisanceEnergy _ _ U
  rw [heq]
  exact hmax z hz

theorem exactSourceCompactEnvelope_point_bound (r : ℕ) (U : Fin r → Covariate d) :
    H r U ≤ (3*Chi^2)^r*eta^4*(B+1)^2 := by
  apply compactNuisanceEnergy_le _ (localNuisanceSet_isCompact _ _ _ _ _ _ _)
    (localNuisanceSet_nonempty _ _ (high_source_interval_numeric C (M : ℝ) hM).2.le
      (by linarith) Q.ρ_pos.le) _
    (fun W y => completeSourcePatchNumerator_continuousOn C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaQ (0 : HighWindowLabels d k) W y)
    (fun _ => (3*Chi^2)^r*eta^4*(B+1)^2) ?_ U
  intro z hz W
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  have ht := crude_raw_square_energy_pointwise Chi eta B
    (highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1).le G.total_positive.le
    (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta z)
    (fun V y => exactSourcePatchNumerator_abs_bound C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaQ r z hz V y) W
  have he : (∑ y : Fin r → Fin 3,
      completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta z W y^2) =
      selectedRawSquareEnergy (completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta z) W := by
    unfold selectedRawSquareEnergy
    apply Finset.sum_congr (by ext y; simp)
    intro y _
    rfl
  exact he.trans_le ht

theorem exactSourceCompactEnvelope_integrable (r : ℕ) : Integrable (H r) (fullSpatialPatchDesign d r) := by
  apply (integrable_const ((3*Chi^2)^r*eta^4*(B+1)^2)).mono'
    (exactSourceCompactEnvelope_measurable C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaQ r).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs, abs_of_nonneg (exactSourceCompactEnvelope_nonneg C hD hq hM Cfr lam ell N mu
    hCfr hell hellN Q eta hk heta hetaQ r U)]
  exact exactSourceCompactEnvelope_point_bound C hD hq hM Cfr lam ell N mu
    hCfr hell hellN Q eta hk heta hetaQ r U

theorem exactSourceCompactEnvelope_integral_eq (r : ℕ) :
    (∫ U, H r U ∂fullSpatialPatchDesign d r) =
      completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r) C Cfr lam ell N mu Q eta :=
  (completeSourceLocalNormSq_eq_patchNorm C Cfr lam ell N mu Q eta).symm

theorem exactSourceLocalNorm_nonneg (r : ℕ) :
    0 ≤ completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r) C Cfr lam ell N mu Q eta := by
  rw [← exactSourceCompactEnvelope_integral_eq C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r]
  exact integral_nonneg (fun U => exactSourceCompactEnvelope_nonneg C hD hq hM Cfr lam ell N mu
    hCfr hell hellN Q eta hk heta hetaQ r U)

theorem exactSourceLocalNorm_geometric_bound (r : ℕ) :
    completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r) C Cfr lam ell N mu Q eta ≤
      (completeSourceCrudeSpatialBase d Chi)^r*eta^4*(B+1)^2 := by
  rw [← exactSourceCompactEnvelope_integral_eq C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r]
  have hi := integral_mono
    (exactSourceCompactEnvelope_integrable C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r)
    (integrable_const ((3*Chi^2)^r*eta^4*(B+1)^2))
    (fun U => exactSourceCompactEnvelope_point_bound C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaQ r U)
  apply hi.trans_eq
  simp only [integral_const, smul_eq_mul, fullSpatialPatchDesign_real_univ]
  unfold completeSourceCrudeSpatialBase
  simp only [mul_pow, pow_mul]
  ring

theorem exactSourceLiteralEnergy_summable (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun r : ℕ => poissonCountWeight x r *
      completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r) C Cfr lam ell N mu Q eta) := by
  apply geometric_poisson_energy_summable hx (completeSourceCrudeSpatialBase_nonneg d Chi)
    (show 0 ≤ eta^4*(B+1)^2 from by positivity)
    (fun r => completeSourceLocalNormSq (D := D) (M := M) (q := q) (n := r) C Cfr lam ell N mu Q eta)
    (fun r => exactSourceLocalNorm_nonneg C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r)
  intro r
  exact (exactSourceLocalNorm_geometric_bound C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r).trans_eq (by ring)

theorem exactSourceLiteralEnergy_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ exactSourceLiteralEnergy (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta x := by
  apply tsum_nonneg
  intro r
  exact mul_nonneg (poissonCountWeight_nonneg hx r)
    (exactSourceLocalNorm_nonneg C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r)

/-- Exact finite spatial energy bounded by the literal infinite energy,
with no volume factor inserted into its Poisson argument. -/
theorem exactSourceCompactEnvelope_finite_energy_le (x : ℝ) (hx : 0 ≤ x) (J : ℕ) :
    (∑ r ∈ Finset.range J, poissonCountWeight x r * ∫ U, H r U ∂fullSpatialPatchDesign d r) ≤
      exactSourceLiteralEnergy (D := D) (M := M) (q := q) C Q Cfr lam ell N mu eta x := by
  simp_rw [exactSourceCompactEnvelope_integral_eq C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ]
  exact (exactSourceLiteralEnergy_summable C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ x hx).sum_le_tsum _
    (fun r _ => mul_nonneg (poissonCountWeight_nonneg hx r)
      (exactSourceLocalNorm_nonneg C hD hq hM Cfr lam ell N mu hCfr hell hellN Q eta hk heta hetaQ r))

end Actual
end NearlyMinimax
