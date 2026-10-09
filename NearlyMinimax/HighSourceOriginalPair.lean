module

public import NearlyMinimax.HighSourceOriginalResponse


@[expose] public section

/-! Actual count-two radial cancellation in the original canonical
periodic-field source, with all response positivity guards derived. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem completeSource_original_count_two {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 2 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ell N mu)),
      ∀ x : Fin 2 → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      ∀ y : Fin 2 → Fin 3,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let eta := cf*(k : ℝ)^(-C.smoothness)
      let c := (highUnionSourceState C R h).2
      let U := fun i : Fin 2 => highLocalCoordinates d k j (x i)
      let g := fun i : Fin 2 => highLocalFieldWithout d k D eta c j (x i)
      let w := fun i : Fin 2 => highPeriodicTensor d k j (x i)
      highUnionSourceMarkedNumerator C R 2 Q.a V eta j h x y =
        eta^2*w 0*w 1*highUnionSourceDensity C R h (x 0)*highUnionSourceDensity C R h (x 1)*
        ((1+N*exactEuclideanDistance (U 0) (U 1))*Real.exp (-(N*exactEuclideanDistance (U 0) (U 1))))*
        ternaryMeanDerivative Q.a (coefficientRegression eta g w (fun i => highFrameFeature (U i)) (c j) 0) (y 0)*
        ternaryMeanDerivative Q.a (coefficientRegression eta g w (fun i => highFrameFeature (U i)) (c j) 1) (y 1) := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta V hV j h x hx y
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf*(k : ℝ)^(-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let U := fun i : Fin 2 => highLocalCoordinates d k j (x i)
  let p := fun i : Fin 2 => highUnionSourceDensity C R h (x i)
  let g := fun i : Fin 2 => highLocalFieldWithout d k D eta c j (x i)
  let w := fun i : Fin 2 => highPeriodicTensor d k j (x i)
  have he := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
    hfr hell hellN hcf heta V hV j h 2 x hx y).1
  have G := completeSourceRows_guards C k D M q hD (by omega) hM Cfr lam ell N mu
    (hfr0.trans hfr) hell hellN
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards C (M : ℝ) hM).1
  have hp (i : Fin 2) : p i ∈ Icc (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) :=
    highUnionSourceDensity_interval C R G h (x i)
  have hU (i : Fin 2) (r : Fin d) : |U i r| ≤ 2 :=
    (highLocalCoordinates_abs_le_one d k j (x i) r).trans (by norm_num)
  have hQ (i : Fin 2) : U i ∈ hyperplaneCube d :=
    highLocalCoordinates_abs_le_one d k j (x i)
  exact he.trans (completeSourceRawNumerator_count_two _ _ lam ell N mu ha hab hell.le hellN.le
    D M q hD hM2 hq Cfr Q.a V eta (by linarith) U hU hQ p g w hp (c j) y)

end NearlyMinimax
