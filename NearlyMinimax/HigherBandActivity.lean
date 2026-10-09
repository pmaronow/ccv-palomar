module

public import NearlyMinimax.HigherBandRows


@[expose] public section

/-! Activity bounds derived from the actual separated cardinal row
measures and finite density/response atom weights. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def higherBandInterpolationCap (d r : ℕ) (lam T : ℝ) : ℝ :=
  2 * (r : ℝ) * (1024 * |lam| * (d : ℝ)^2)^(r-1) * T^2 * (1+Real.log T)^(r-2)

theorem higherBandInterpolationCap_nonneg (d r : ℕ) (lam T : ℝ) (hT : 1 ≤ T) :
    0 ≤ higherBandInterpolationCap d r lam T := by
  have hlog : 0 ≤ 1 + Real.log T := add_nonneg (by norm_num) (Real.log_nonneg hT)
  unfold higherBandInterpolationCap
  positivity

theorem higherBandCarrier_cost_integral_le (d r D : ℕ) (hr : 2 ≤ r)
    (lam L T : ℝ) (hT : 1 ≤ T) (hLT : L ≤ T) (fine : Bool) :
    (∫ ζ, separatedMatrixCost (higherBandCarrierAmplitude d r D lam fine) ζ
      ∂higherBandCarrierMeasure d r L T fine) ≤ higherBandInterpolationCap d r lam T := by
  cases fine
  · have h := cardinal_separated_cost_integral_le (d := d) (D := D) hr lam hT
    have hb : 0 ≤ (r : ℝ) * (1024 * |lam| * (d : ℝ)^2)^(r-1) * T^2 * (1+Real.log T)^(r-2) := by
      have hlog : 0 ≤ 1 + Real.log T := add_nonneg (by norm_num) (Real.log_nonneg hT)
      positivity
    exact h.trans (by dsimp [higherBandInterpolationCap]; nlinarith)
  · exact cardinal_band_cost_integral_le hr lam L hT hLT

def ordinaryDensityActivityBase (a b : ℝ) : ℝ :=
  Real.exp (1 + exteriorTau ((a+b)/(b-a))) * |b / densityMargin a b 0|

def higherBandRowActivityCap (d r m D q : ℕ) (a b C lam T : ℝ) : ℝ :=
  (ordinaryDensityActivityBase a b)^r * (D : ℝ)^r *
    Real.exp ((m : ℝ) * exteriorTau ((a+b)/(b-a))) *
    (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) * higherBandInterpolationCap d r lam T

/-- The bound on the actual activation mass follows from actual atom
variation and genuine positive separated-representation cost. -/
theorem higherBandRowMass_le_activityCap (d r m D q : ℕ) (hr : 2 ≤ r) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C lam L T : ℝ)
    (hT : 1 ≤ T) (hLT : L ≤ T) (fine : Bool) :
    higherBandRowMass d r m D q a b C lam L T fine ≤ higherBandRowActivityCap d r m D q a b C lam T := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  rw [higherBandRowMass_eq_variation d r m D q a b C lam L T hT fine]
  have h := highPacketSignedMeasure_exponential_cost (higherBandCarrierMeasure d r L T fine)
    a b ha hab m r D q (by omega) hD C (higherBandCarrierAmplitude d r D lam fine)
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
  apply h.trans
  change _ ≤ _ * higherBandInterpolationCap d r lam T
  apply mul_le_mul_of_nonneg_left
  · exact higherBandCarrier_cost_integral_le d r D hr lam L T hT hLT fine
  · positivity

theorem higherBandRowActivation_le_activityCap (d r m D q : ℕ) (hr : 2 ≤ r) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C lam L T : ℝ)
    (hT : 1 ≤ T) (hLT : L ≤ T) (fine : Bool) (e : HigherBandRowMark d r m D q fine) :
    |higherBandRowActivation d r m D q a b C lam L T fine e| ≤
      higherBandRowActivityCap d r m D q a b C lam T :=
  (higherBandRowActivation_bound d r m D q a b C lam L T fine e).trans
    (higherBandRowMass_le_activityCap d r m D q hr hD a b ha hab C lam L T hT hLT fine)

end NearlyMinimax
