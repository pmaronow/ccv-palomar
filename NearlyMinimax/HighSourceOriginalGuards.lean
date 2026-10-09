module

public import NearlyMinimax.HighCompleteSourceMarkedTail
public import NearlyMinimax.HighSourceCanonicalResponse
public import NearlyMinimax.HighSourceFinalDecomposition


@[expose] public section

/-! Primitive local response guards derived uniformly from the actual
periodic frame and canonical source. Constants are fixed before the grid,
selector orders, history and sample configuration. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

structure HighFrameOriginalLocalGuards (d k D : ℕ) [NeZero k] (Cfr eta rho : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) : Prop where
  amplitude_nonneg : 0 ≤ eta
  amplitude_half : eta ≤ rho/2
  coefficient_ball : ∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹
  weight_abs : ∀ j x, |highPeriodicTensor d k j x| ≤ 1
  without_abs : ∀ j x, |highLocalFieldWithout d k D eta c j x| ≤ rho/2
  profile_abs : ∀ j (v : HighFrameIndex d D → ℝ), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |∑ γ, highLocalFrameFeature k j x γ*v γ| ≤ 1
  regression_abs : ∀ j (v : HighFrameIndex d D → ℝ), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |highLocalFieldWithout d k D eta c j x + eta*highPeriodicTensor d k j x*
      (∑ γ, highLocalFrameFeature k j x γ*v γ)| ≤ rho

theorem highFrame_original_local_guards {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ Cfr cf : ℝ,
      Cfr0 ≤ Cfr → 0 ≤ cf → cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      ∀ c : HighWindowLabels d k → HighFrameIndex d D → ℝ,
      (∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹) →
      HighFrameOriginalLocalGuards d k D Cfr (cf*(k : ℝ)^(-C.smoothness)) Q.ρ c := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let eta0 := Q.ρ/(2*((2 : ℝ)^d+1))
  refine ⟨Cfr0,eta0,hfr0,div_pos Q.ρ_pos (by positivity),?_⟩
  intro k D hk0 hk Cfr cf hfr hcf heta c hc
  letI := hk0
  let eta := cf*(k : ℝ)^(-C.smoothness)
  have hfr1 : 1 ≤ Cfr := hfr0.trans hfr
  have hen : 0 ≤ eta := by dsimp [eta]; positivity
  have hamp : ((2 : ℝ)^d+1)*eta ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*((2 : ℝ)^d+1))).mp heta
    change eta*(2*((2 : ℝ)^d+1)) ≤ Q.ρ at ht
    nlinarith
  have hehalf : eta ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (j) : frameCoefficientL1 (highFramePolynomial (c j)) ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (hc j).trans ((inv_le_inv₀ (by linarith : 0 < Cfr) (by linarith : 0 < Cfr0)).mpr hfr)
  have hF := (hfield k hk0 hk cf hcf (fun j => highFramePolynomial (c j)) hP).1
  have hw (j) (x) : |highPeriodicTensor d k j x| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j x)]
    exact highPeriodicTensor_le_one d k (by omega) j x
  have hprof (j) (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |∑ γ, highLocalFrameFeature k j x γ*v γ| ≤ 1 :=
    highLocalFrameFeature_ball_abs_le_one k j x Cfr hfr1 v hv
  have hterm (j) (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |eta*highPeriodicTensor d k j x*(∑ γ, highLocalFrameFeature k j x γ*v γ)| ≤ eta := by
    rw [abs_mul,abs_mul,abs_of_nonneg hen]
    have ht := mul_le_mul (hw j x) (hprof j v hv x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left ht hen]
  have hg (j) (x) : |highLocalFieldWithout d k D eta c j x| ≤ Q.ρ/2 := by
    have hd := highFrameField_local_decomposition d k D hk eta c j x
    have he : highLocalFieldWithout d k D eta c j x =
        highFrameField d k eta (fun l => highFramePolynomial (c l)) x -
          eta*highPeriodicTensor d k j x*(∑ γ, highLocalFrameFeature k j x γ*c j γ) := by
      linarith [hd]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hF x) (hterm j (c j) (hc j) x)).trans
      (by nlinarith only [hamp]))
  refine ⟨hen,hehalf,hc,hw,hg,hprof,?_⟩
  intro j v hv x
  exact (abs_add_le _ _).trans (by linarith only [hg j x,hterm j v hv x,hehalf])

theorem completeSource_original_local_guards {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ell N mu)),
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      HighFrameOriginalLocalGuards d k D Cfr (cf*(k : ℝ)^(-C.smoothness)) Q.ρ
        (highUnionSourceState C R h).2 := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hguards⟩ := highFrame_original_local_guards C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu
    (hfr0.trans hfr) hell hellN
  exact hguards k D hk0 hk Cfr cf hfr hcf heta (highUnionSourceState C R h).2
    (highUnionSourceState_coefficient_ball C R G h)

theorem HighFrameOriginalLocalGuards.ternary_floor {d k D : ℕ}
    [NeZero k] {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C)
    {Cfr eta V : ℝ} {c : HighWindowLabels d k → HighFrameIndex d D → ℝ}
    (H : HighFrameOriginalLocalGuards d k D Cfr eta Q.ρ c)
    (hV : |V-Q.v| ≤ Q.ρ) (j : HighWindowLabels d k)
    (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹)
    (x : Covariate d) (y : Fin 3) :
    Q.c ≤ highMarkedResponseMass Q.a V eta (highLocalFieldWithout d k D eta c j)
      (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) v x y := by
  exact (Q.legal _ V (H.regression_abs j v hv x) hV).2.2.1 y

end NearlyMinimax
