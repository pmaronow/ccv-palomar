module

public import NearlyMinimax.HighUnionRawFisherExact
public import NearlyMinimax.HighWindowFactorialEnergy


@[expose] public section

/-! Exact original chart coefficients convert the genuine finite source
Fisher series into the literal infinite local energy, without inflating
C_sharp. This finite-to-infinite step uses true summability. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem highSourceSpatialSeriesExact_const_le_tsum {d k : ℕ} [NeZero k]
    (n : ℕ) (pMinus cMass : ℝ) (hp : 0 < pMinus) (hc : 0 < cMass)
    (H : (r : ℕ) → (Fin r → Covariate d) → ℝ) (hH0 : ∀ r U, 0 ≤ H r U)
    (hsum : Summable (fun r : ℕ => poissonCountWeight
      ((n : ℝ)*highFixedScoreDenominator pMinus cMass*(1/(k : ℝ))^d) r *
        ∫ U, H r U ∂fullSpatialPatchDesign d r)) :
    highSourceSpatialSeriesExact d k n pMinus cMass (fun _ => H) ≤
      (3^d : ℕ)*(k : ℝ)^d *
        ∑' r : ℕ, poissonCountWeight
          ((n : ℝ)*highFixedScoreDenominator pMinus cMass*(1/(k : ℝ))^d) r *
            ∫ U, H r U ∂fullSpatialPatchDesign d r := by
  let f := fun r : ℕ => poissonCountWeight
    ((n : ℝ)*highFixedScoreDenominator pMinus cMass*(1/(k : ℝ))^d) r *
      ∫ U, H r U ∂fullSpatialPatchDesign d r
  have hf (r : ℕ) : 0 ≤ f r := mul_nonneg
    (poissonCountWeight_nonneg (by positivity [high_fixed_score_denominator_pos hp hc]) r)
    (integral_nonneg (hH0 r))
  have hfinite : (∑ r ∈ Finset.range (n+1), f r) ≤ ∑' r : ℕ, f r :=
    Summable.sum_le_tsum (Finset.range (n+1)) (fun r _ => hf r) hsum
  unfold highSourceSpatialSeriesExact
  simp only [Finset.sum_const, Finset.card_univ, highWindowLabels_card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  change (3 : ℝ)^d*((k : ℝ)^d*(∑ r ∈ Finset.range (n+1), f r)) ≤ _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left hfinite (by positivity)

end NearlyMinimax
