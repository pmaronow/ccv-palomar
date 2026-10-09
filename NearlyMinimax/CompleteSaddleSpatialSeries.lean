module

public import NearlyMinimax.CompleteSaddleEnergy
public import NearlyMinimax.HighWindowFactorialEnergy
public import NearlyMinimax.HighUnionRawFisher


@[expose] public section

/-! Exact finite-window accounting for the concrete saddle envelope. The
full source series has the factor 3^d k^d and the proved actual factorial
energy budget. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem completeSaddleSpatialSeries_eq {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ)
    [NeZero (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω n)] :
    highSourceSpatialSeries d (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω n) n C.densityLower Q.c
      (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) =
    (3^d : ℕ)*(lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d *
      (∑ r ∈ Finset.range (n+1), poissonCountWeight
        (completeSaddleScoreFactor C Q*completeSaddleMu C Cω n) r *
        ∫ u, completeSaddleGeometryEnvelope C Q Cfr cf Cω n r u ∂fullSpatialPatchDesign d r) := by
  let k := lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω n
  have hmu : completeSaddleMu C Cω n = (n : ℝ)/(k : ℝ)^d := by
    dsimp only [completeSaddleMu,lowerSaddleMu,lowerSaddleH,k]
    rw [Real.rpow_natCast,inv_pow]
    rfl
  have hparameter : (n : ℝ)*highFixedScoreDenominator C.densityLower Q.c*(2/(k : ℝ))^d =
      completeSaddleScoreFactor C Q*completeSaddleMu C Cω n :=
    high_design_factorial_parameter (highFixedScoreDenominator C.densityLower Q.c)
      (completeSaddleMu C Cω n) hmu
  change highSourceSpatialSeries d k n C.densityLower Q.c _ = _
  simp only [highSourceSpatialSeries,hparameter,Finset.sum_const,Finset.card_univ,
    highWindowLabels_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  simp only [poissonCountWeight,fullSpatialPatchDesign]
  ring

theorem eventually_completeSaddleSpatialSeries_le {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf : ℝ} (hcf : 0 < cf) (Cfr Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ hk0 : NeZero (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n),
      highSourceSpatialSeries d (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n) n C.densityLower Q.c
        (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) ≤
      (3^d : ℕ)*(lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d *
          completeSaddleEnergyBudget C Q Cfr cf Cω n := by
  filter_upwards [eventually_completeSaddleGeometry_factorial C Q hs hd hcf Cfr Cω] with n hn
  intro hk0
  letI := hk0
  rw [completeSaddleSpatialSeries_eq]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

end NearlyMinimax
