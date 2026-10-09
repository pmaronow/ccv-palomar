module

public import NearlyMinimax.HighSourceOriginalGuards


@[expose] public section

/-! Direct original-model response identities for the canonical complete
source. Uniform ternary positivity is derived from the actual periodic
field, and low-count cancellation has no supplied response guard. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem completeSource_original_response_exact_and_low_counts {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ell N mu)),
      ∀ n : ℕ, ∀ x : Fin n → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      ∀ y : Fin n → Fin 3,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let eta := cf*(k : ℝ)^(-C.smoothness)
      let c := (highUnionSourceState C R h).2
      highUnionSourceMarkedNumerator C R n Q.a V eta j h x y =
        completeSourceRawNumerator (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ))
          lam ell N mu D M q Cfr Q.a V eta (fun i => highLocalCoordinates d k j (x i))
          (fun i => highUnionSourceDensity C R h (x i))
          (fun i => highLocalFieldWithout d k D eta c j (x i))
          (fun i => highPeriodicTensor d k j (x i)) (c j) y ∧
        (n ≤ 1 → highUnionSourceMarkedNumerator C R n Q.a V eta j h x y = 0) := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hguards⟩ := completeSource_original_local_guards C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta V hV j h n x hx y
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf*(k : ℝ)^(-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let U := fun i : Fin n => highLocalCoordinates d k j (x i)
  let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
  let g := fun i : Fin n => highLocalFieldWithout d k D eta c j (x i)
  let w := fun i : Fin n => highPeriodicTensor d k j (x i)
  have hfr1 := hfr0.trans hfr
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hfr1 hell hellN
  have H := hguards k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h
  have hmass (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (i : Fin n) (b : Fin 3) :
      0 ≤ ternaryMass Q.a
        (coefficientRegression eta g w (fun u : Fin n => highLocalFrameFeature k j (x u)) v i) V b := by
    have hf := H.ternary_floor Q hV j v hv (x i) b
    exact Q.c_pos.le.trans hf
  have he := completeSourceRawNumerator_eq_canonical C hD hq hM Cfr lam ell N mu
    hfr1 hell hellN j h x hx Q.a V eta Q.a_pos.ne' g w hmass y
  change highUnionSourceMarkedNumerator C R n Q.a V eta j h x y =
    completeSourceRawNumerator _ _ lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y at he
  refine ⟨he,?_⟩
  intro hn
  rw [he]
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hp (i : Fin n) : p i ∈ Icc (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) :=
    highUnionSourceDensity_interval C R G h (x i)
  have hU (i : Fin n) (r : Fin d) : |U i r| ≤ 2 :=
    (highLocalCoordinates_abs_le_one d k j (x i) r).trans (by norm_num)
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl
  · exact completeSourceRawNumerator_count_zero _ _ lam ell N mu ha hab D M q (by omega)
      Cfr Q.a V eta U p g w (c j) y
  · exact completeSourceRawNumerator_count_one _ _ lam ell N mu ha hab D M q (by omega) hq
      Cfr Q.a V eta (by linarith) U hU p g w hp (c j) y

end NearlyMinimax
