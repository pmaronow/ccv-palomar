module

public import NearlyMinimax.HighCompleteSourceTail


@[expose] public section

/-! The all-count numerator cap for the actual periodic source field.
Frame and amplitude thresholds are fixed before the grid, selector orders,
history, and extension domain. No field/profile/cap premise remains. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem completeSourceNumerator_original_field_bound {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 η0 : ℝ, 1 ≤ Cfr0 ∧ 0 < η0 ∧
      ∀ k D M q n : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → 1 ≤ n →
      highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ℓ N μ cf : ℝ, Cfr0 ≤ Cfr → 0 < ℓ → ℓ < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ η0 →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)),
      ∀ x : Fin n → Covariate d, ∀ y : Fin n → Fin 3,
      let R := completeSourceRows C k D M q Cfr lam ℓ N μ
      let η := cf*(k : ℝ)^(-C.smoothness)
      let c := (highUnionSourceState C R h).2
      |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
        (highUnionActivation R (highCenterMix C)) Q.a V η
        (fun u => highUnionSourceDensity C R h (x u))
        (fun e u => highUnionSourceResetDensity C R j h e (x u))
        (highUnionSourceResetCoefficient C R j h)
        (fun u => highLocalFieldWithout d k D η c j (x u))
        (fun u => highPeriodicTensor d k j (x u))
        (fun u => highLocalFrameFeature k j (x u)) (c j) y| ≤
        (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)^n*
          η^2*(highRowTotalMass R.rowMass+1) := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let η0 := Q.ρ/(2*((2 : ℝ)^d+1))
  have hη0 : 0 < η0 := div_pos Q.ρ_pos (by positivity)
  refine ⟨Cfr0,η0,hfr0,hη0,?_⟩
  intro k D M q n hk0 horder hk hD hq hn hM Cfr lam ℓ N μ cf hfr hℓ hℓN hcf hη V hV j h x y
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ (hfr0.trans hfr) hℓ hℓN
  let c := (highUnionSourceState C R h).2
  let η := cf*(k : ℝ)^(-C.smoothness)
  let g := fun u : Fin n => highLocalFieldWithout d k D η c j (x u)
  let w := fun u : Fin n => highPeriodicTensor d k j (x u)
  let φ : Fin n → HighFrameIndex d D → ℝ := fun u => highLocalFrameFeature k j (x u)
  have hηn : 0 ≤ η := by dsimp [η]; positivity
  have hamp : ((2 : ℝ)^d+1)*η ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*((2 : ℝ)^d+1))).mp hη
    nlinarith
  have hηρ : η ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (l) : frameCoefficientL1 (highFramePolynomial (c l)) ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (highUnionSourceState_coefficient_ball C R G h l).trans
      ((inv_le_inv₀ (by linarith : 0 < Cfr) (by linarith : 0 < Cfr0)).mpr hfr)
  have hF := (hfield k hk0 hk cf hcf (fun l => highFramePolynomial (c l)) hP).1
  have hw (u) : |w u| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j (x u))]
    exact highPeriodicTensor_le_one d k (by omega) j (x u)
  have hφ (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (u) :
      |∑ γ, φ u γ*v γ| ≤ 1 :=
    highLocalFrameFeature_ball_abs_le_one k j (x u) Cfr (hfr0.trans hfr) v hv
  have hg (u) : |g u| ≤ Q.ρ/2 := by
    have hprof := hφ (c j) (highUnionSourceState_coefficient_ball C R G h j) u
    have hh : |η*w u*(∑ γ, φ u γ*c j γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hηn]
      have ht := mul_le_mul (hw u) hprof (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left ht hηn]
    have hd := highFrameField_local_decomposition d k D hk η c j (x u)
    have he : g u = highFrameField d k η (fun l => highFramePolynomial (c l)) (x u)-
        η*w u*(∑ γ, φ u γ*c j γ) := by dsimp [g,w,φ]; linarith [hd]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hF (x u)) hh).trans (by nlinarith only [hamp]))
  exact completeSourceNumerator_all_count_exponential_bound C hD hq hM Cfr lam ℓ N μ
    (hfr0.trans hfr) hℓ hℓN hn j h Q.a V η Q.ρ Q.a_pos hηn Q.ρ_pos.le hηρ x g w φ
    hg hw hφ (fun f hf z => Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 z)) y

end NearlyMinimax
