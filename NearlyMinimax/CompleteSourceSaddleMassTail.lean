module

public import NearlyMinimax.CompleteSourceInvariantMass
public import NearlyMinimax.HighUnionTiltedTail
public import NearlyMinimax.HighMassTailScale


@[expose] public section

/-! Genuine exceptional-mass tails of the complete singleton/pair/higher
row prior, specialized to the actual rounded lower saddle. The deterministic
envelope is fixed before the extension domain and all source times. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

section Pointwise
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ell N mu : ℝ) (hCfr : 1 ≤ Cfr) (hell : 0 < ell) (hellN : ell < N)
include hD hq hM hCfr hell hellN

/-- Every time of the actual complete-row source has the genuine tilted
exceptional bound. All mass-law and local cancellation premises are
discharged by the true complete packet construction. -/
theorem completeSourceMass_prior_tilted_tail (hk : 2 ≤ k) (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T*(highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass /
      highCenterMix C)/historyReferenceRho (3^d) ≤ 1/(2+8*((3^d:ℕ):ℝ)^2))
    (n : ℕ) (epsilon : ℝ)
    (hepsilon : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ epsilon)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C)))
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu)) n).real
      {h | epsilon < |highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu) h-1|} ≤
      2*Real.exp (-epsilon^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _ (highUnionSourceMass_measurable C _ G) n
    (completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht) epsilon]
  exact highUnionSourceMass_reference_tilted_tail C _ G hk n epsilon hepsilon

end Pointwise

/-- The fixed canonical source coefficient; it depends only on model constants. -/
def highCompleteSourceSaddleCoefficient {d : ℕ} (C : ModelConstants d) : ℝ :=
  lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

def highCompleteSourceSaddleTheta {d : ℕ} (C : ModelConstants d) : ℝ :=
  lowerSaddleTheta C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

/-- The actual geometric envelope for the complete-row tilted bad mass. -/
def highCompleteSourceSaddleTail {d : ℕ} (C : ModelConstants d) (Cω cm : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleExceptionalTail d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
    (cm^2/(8*highHistoryMassMomentConstant d C.densityLower C.densityUpper)) n

theorem highCompleteSourceSaddleTail_nonneg {d : ℕ} (C : ModelConstants d) (Cω cm : ℝ) (n : ℕ) :
    0 ≤ highCompleteSourceSaddleTail C Cω cm n := by
  unfold highCompleteSourceSaddleTail lowerSaddleExceptionalTail
  positivity

/-- The genuine source envelope is o(Psi²), with the paper's exact exponent,
stretched exponential and lower logarithmic power. -/
theorem highCompleteSourceSaddleTail_over_Psi_tends_zero {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ)) {cm : ℝ} (hcm : 0 < cm) (Cω : ℝ) :
    Tendsto (fun n : ℕ => highCompleteSourceSaddleTail C Cω cm n /
      (rateScale (rateExponent C.smoothness d)
        (stretchConstant C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper))
        (lowerLogPower C.smoothness d) n)^2) atTop (𝓝 0) := by
  exact (actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero hs hd C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hcm
    (highHistoryMassMomentConstant_pos d _ _ (C.densityLower_lt_one.trans C.one_lt_densityUpper)) Cω).comp
      tendsto_natCast_atTop_atTop

/-- Uniform complete-row saddle tail bound. The envelope is chosen before
all legal packet parameters, every source time, and every extension domain;
its mass-law invariance and MGF are consequences of the actual construction. -/
theorem eventually_completeSource_saddle_mass_tail {d : ℕ} [NeZero d] (C : ModelConstants d)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ)) {cm : ℝ} (hcm : 0 < cm) (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      k = lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n →
      M = lowerSaddleM (highCompleteSourceSaddleCoefficient C) n →
      ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ Cfr lam ell N mu : ℝ, ∀ hCfr : 1 ≤ Cfr, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      ∀ T : ℝ, ∀ hT : 0 ≤ T,
      ∀ hsmall : T*(highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass /
        highCenterMix C)/historyReferenceRho (3^d) ≤ 1/(2+8*((3^d:ℕ):ℝ)^2),
      ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      (massPowerTilt
        (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
          (highUnionLaw (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C))
          (highUnionActivation (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C)))
        (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu)) n).real
        {h | cm/(M : ℝ) < |highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu) h-1|} ≤
        highCompleteSourceSaddleTail C Cω cm n := by
  have hτ := densityIntervalExponent_pos C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
  have hm : 0 < highCompleteSourceSaddleCoefficient C := lowerSaddleCoefficient_pos hs hd hτ
  have hθ : 0 < highCompleteSourceSaddleTheta C := lowerSaddleTheta_pos hs hd hτ
  have hg := (eventually_highHistoryMass_saddle_guard (NeZero.pos d) hm hθ hcm Cω
    C.densityLower C.densityUpper (C.densityLower_lt_one.trans C.one_lt_densityUpper))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hg] with n hn
  intro k D M q hk horder hkgrid hMdegree hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht
  letI := hk
  letI := horder
  have heps : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n : ℝ) ≤ cm/(M : ℝ) := by
    simpa only [hkgrid,hMdegree] using hn.2
  have hkg : 2 ≤ k := by simpa only [hkgrid] using hn.1
  have hb := completeSourceMass_prior_tilted_tail C hD hq hM Cfr lam ell N mu hCfr hell hellN
    hkg T hT hsmall n (cm/(M : ℝ)) heps t ht
  apply hb.trans_eq
  rw [hkgrid,hMdegree]
  exact highHistoryMass_saddle_tail_eq d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cm C.densityLower C.densityUpper n

end NearlyMinimax
