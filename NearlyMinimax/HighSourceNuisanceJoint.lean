module

public import NearlyMinimax.HighSourceNuisanceNorm


@[expose] public section

/-! Joint Borel dependence of the actual patch numerator on legal nuisance
parameters and spatial observations. The general Caratheodory theorem avoids
unfolding the complete source's dependent row carrier. -/
noncomputable section
open Set MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
section
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ell N mu : ℝ) (hCfr : 1 ≤ Cfr) (hell : 0 < ell) (hellN : ell < N)
  (Q : LowSmoothnessTernaryConstants C) (eta : ℝ) (hk : 4 ≤ k)
  (heta : 0 ≤ eta) (hetaRho : eta ≤ Q.ρ/2)

local notation "K" => localNuisanceSet (HighFrameIndex d D) n
  (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr Q.ρ Q.v

include hD hq hM hCfr hell hellN hk heta hetaRho

theorem completeSourcePatchNumerator_joint_measurable
    (j : HighWindowLabels d k) (y : Fin n → Fin 3) :
    Measurable (fun zU : K × (Fin n → Covariate d) =>
      completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta
        zU.1.val zU.2 y) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (fun U => (completeSourcePatchNumerator_continuousOn C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaRho j U y).domRestrict)
    (fun z : K => completeSourcePatchNumerator_measurable C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaRho j z.val z.property y)

theorem completeSourcePatchNumerator_joint_response_measurable
    (j : HighWindowLabels d k) :
    Measurable (fun p : (K × (Fin n → Covariate d)) × (Fin n → Fin 3) =>
      completeSourcePatchNumerator (M := M) (q := q) C Cfr lam ell N mu Q eta
        p.1.1.val p.1.2 p.2) := by
  exact measurable_from_prod_countable_left (fun y =>
    completeSourcePatchNumerator_joint_measurable C hD hq hM Cfr lam ell N mu
      hCfr hell hellN Q eta hk heta hetaRho j y)

end
end NearlyMinimax
