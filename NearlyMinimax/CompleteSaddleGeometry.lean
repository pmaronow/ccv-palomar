module

public import NearlyMinimax.HighSourceAllGeometry
public import NearlyMinimax.HighGeometryEnvelopeMonotone
public import NearlyMinimax.OrdinaryFineAliasSaddleEnvelope


@[expose] public section

/-! The concrete geometry-only envelope at the actual rounded source
saddle. Its count profile uses the true normalized activation budget. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local instance] Classical.propDecidable

 def completeSaddleGeometryEnvelope {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ) :
    (r : ℕ) → (Fin r → Covariate d) → ℝ :=
  let q := lowerSaddleResponseOrder C.smoothness d
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let M := lowerSaddleM m n
  let D := lowerSaddleD d m n
  let N := lowerSaddleN C.smoothness d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) n
  let mu := lowerSaddleMu d m theta Cω n
  let ell := lowerAliasCutoff C.smoothness d m theta Cω c0 (shrunkDensityExponent C.densityLower C.densityUpper) n
  let eta := lowerSaddleEta C.smoothness d m theta Cω cf n
  let Rbound := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  let Bl := completeSourceSaddleActivity C q Cfr (spatialInterpolationLambda d) Cω n
  completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta Chi Bl

 theorem completeSaddleGeometryEnvelope_nonneg {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n r : ℕ) (U : Fin r → Covariate d) :
    0 ≤ completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U :=
  by
    unfold completeSaddleGeometryEnvelope
    exact completeSourceGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r U

 theorem completeSaddleGeometryEnvelope_measurable {d : ℕ} [NeZero d] (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n r : ℕ)
    (hell : 1 ≤ lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω (densityIntervalExponent C.densityLower C.densityUpper+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) n) :
    Measurable (completeSaddleGeometryEnvelope C Q Cfr cf Cω n r) :=
  by
    unfold completeSaddleGeometryEnvelope
    apply completeSourceGeometryEnvelope_measurable
    exact hell

 theorem completeSaddleGeometryEnvelope_integrable {d : ℕ} [NeZero d] (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (hd : 5 ≤ d) (Cfr cf Cω : ℝ) (n r : ℕ)
    (hell : 1 ≤ lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω (densityIntervalExponent C.densityLower C.densityUpper+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) n)
    (hellN : lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω (densityIntervalExponent C.densityLower C.densityUpper+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) n ≤
      lowerSaddleN C.smoothness d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) n) :
    Integrable (completeSaddleGeometryEnvelope C Q Cfr cf Cω n r) (fullSpatialPatchDesign d r) :=
  by
    unfold completeSaddleGeometryEnvelope
    apply completeSourceGeometryEnvelope_integrable hd
    · exact hell
    · exact hellN

end NearlyMinimax
