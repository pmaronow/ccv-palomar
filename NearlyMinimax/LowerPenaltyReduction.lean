module

public import NearlyMinimax.LowerRawCostReduction


@[expose] public section

/-! The genuine mass-exception penalty is negligible compared with the
squared lower saddle scale. Constants are fixed before any model domain. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The exact numeric lower envelope, after the true tilted exceptional
penalty, dominates a fixed positive multiple of the manuscript's squared
scale. No statistical risk or desired-rate premise is used. -/
theorem eventually_actual_lowerSaddle_penalized_rate_square
    {s d a b cf CG ctr cm Cmgf DV : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hcf : 0 < cf) (hCG : 0 < CG) (hctr : 0 < ctr)
    (hcm : 0 < cm) (hCmgf : 0 < Cmgf) (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let τM := shrunkDensityExponent a b
      (c*rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x)^2 ≤
      ctr/(3*CG)*(lowerSaddleRisk s d m θ C cf τM x)^2-
        DV^2*lowerSaddleExceptionalTail d m θ C (cm^2/(8*Cmgf)) x := by
  obtain ⟨c₀,A,hc₀,hA,hbracket⟩ := actual_lowerSaddleRisk_rate_bracket hs hd ha hab hcf C
  let α := ctr/(3*CG)
  have hα : 0 < α := by dsimp [α]; positivity
  let q := α*c₀^2/2
  have hq : 0 < q := by dsimp [q]; positivity
  let c := Real.sqrt q
  have hc : 0 < c := Real.sqrt_pos.mpr hq
  have hcsq : c^2 = q := Real.sq_sqrt hq.le
  have htol : 0 < q/(DV^2+1) := by positivity
  have ht := (actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero
    hs hd ha hab hcm hCmgf C).eventually (eventually_lt_nhds htol)
  refine ⟨c,hc,?_⟩
  filter_upwards [hbracket,ht] with x hb hx
  dsimp only at hb hx ⊢
  let S := rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
    (lowerLogPower s d) x
  let R := lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
    (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x
  let ε := lowerSaddleExceptionalTail d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
    (lowerSaddleTheta s d (densityIntervalExponent a b)) C (cm^2/(8*Cmgf)) x
  have hS : 0 < S := rateScale_pos _ _ _ _
  have hR : 0 < R := lowerSaddleRisk_positive hcf _
  have hlow : c₀*S ≤ R := hb.1
  have hsq : (c₀*S)^2 ≤ R^2 := (sq_le_sq₀ (by positivity) hR.le).mpr hlow
  have hε : ε ≤ (q/(DV^2+1))*S^2 := by
    apply (div_le_iff₀ (by positivity : 0 < S^2)).mp
    exact hx.le
  have hfrac : DV^2*(q/(DV^2+1)) ≤ q := by
    have hp : 0 ≤ q := hq.le
    have he : DV^2*(q/(DV^2+1)) = (DV^2*q)/(DV^2+1) := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < DV^2+1)).mpr
    nlinarith only [hp]
  have hp1 := mul_le_mul_of_nonneg_left hε (sq_nonneg DV)
  have hp2 := mul_le_mul_of_nonneg_right hfrac (sq_nonneg S)
  have hpen : DV^2*ε ≤ q*S^2 := by nlinarith only [hp1,hp2]
  have hmain := mul_le_mul_of_nonneg_left hsq hα.le
  change (c*S)^2 ≤ α*R^2-DV^2*ε
  rw [mul_pow,hcsq]
  dsimp [q] at hpen ⊢
  nlinarith only [hpen,hmain]

end NearlyMinimax
