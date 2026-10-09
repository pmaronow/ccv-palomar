module

public import NearlyMinimax.HighCompleteSourceSpatialTail


@[expose] public section

/-! Large-count factorial energy of the genuine canonical complete source
in the original periodic-frame field. All source field guards are derived;
the fixed tail constant precedes degree, count, history and spatial grid. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem crude_raw_square_energy_pointwise {d n : ℕ} (Chi η B : ℝ)
    (hChi : 0 ≤ Chi) (hB : 0 ≤ B)
    (R : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (hcap : ∀ x y, |R x y| ≤ Chi^n*η^2*(B+1)) (x : Fin n → Covariate d) :
    selectedRawSquareEnergy R x ≤ (3*Chi^2)^n*η^4*(B+1)^2 := by
  have hp (y) : R x y ^ 2 ≤ Chi^(2*n)*η^4*(B+1)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Chi^n*η^2*(B+1))).mpr (hcap x y)
    simp only [sq_abs] at hh
    convert hh using 1 <;> (try rw [mul_pow,mul_pow,←pow_mul]) <;> ring
  have he : selectedRawSquareEnergy R x = ∑ y : Fin n → Fin 3, R x y ^ 2 := by
    unfold selectedRawSquareEnergy
    apply Finset.sum_congr (by ext y; simp)
    intro y _
    rfl
  calc
    _ = ∑ y : Fin n → Fin 3, R x y ^ 2 := he
    _ ≤ ∑ _y : Fin n → Fin 3, Chi^(2*n)*η^4*(B+1)^2 :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = (3*Chi^2)^n*η^4*(B+1)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow, Nat.cast_ofNat, nsmul_eq_mul, mul_pow, ←pow_mul]
      ring

section Marked
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
  [NeZero k] [LinearOrder (HighWindowLabels d k)]

def highUnionSourceMarkedNumerator (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    (n : ℕ) (a V η : ℝ) (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) : ℝ :=
  highMarkedSampleNumerator n (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) a V η
    (highUnionSourceDensity C R h) (highUnionSourceResetDensity C R j h)
    (highUnionSourceResetCoefficient C R j h)
    (highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
    ((highUnionSourceState C R h).2 j) x y

theorem highUnionSourceMarkedNumerator_measurable (C : ModelConstants d)
    (R : HighUnionRowData d k D I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (n : ℕ) (a V η : ℝ) (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (y : Fin n → Fin 3) : Measurable (fun x => highUnionSourceMarkedNumerator C R n a V η j h x y) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  exact highMarkedSampleNumerator_measurable n (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) (highUnionActivation_measurable R G.activation_measurable _)
    a V η (highUnionSourceDensity C R h)
    ((highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id))
    (highUnionSourceResetDensity C R j h) (highUnionSourceResetDensity_measurable C R G j h)
    (highUnionSourceResetCoefficient C R j h) (highUnionSourceResetCoefficient_measurable C R G j h)
    (highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor d k j) (highLocalFieldWithout_continuous d k D η _ j).measurable
    (highPeriodicTensor_contDiff d k j).continuous.measurable (fun x => highLocalFrameFeature k j x)
    (highLocalFrameFeature_measurable k j) ((highUnionSourceState C R h).2 j) y

end Marked

theorem completeSourceMarkedNumerator_original_spatial_bound {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 η0 : ℝ, 1 ≤ Cfr0 ∧ 0 < η0 ∧
      ∀ k D M q n : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → 1 ≤ n →
      highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ℓ N μ cf : ℝ, Cfr0 ≤ Cfr → 0 < ℓ → ℓ < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ η0 →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)),
      let R := completeSourceRows C k D M q Cfr lam ℓ N μ
      let η := cf*(k : ℝ)^(-C.smoothness)
      let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
      Integrable (selectedRawSquareEnergy (highUnionSourceMarkedNumerator C R n Q.a V η j h))
        (fullSpatialPatchDesign d n) ∧
      (∫ x, selectedRawSquareEnergy (highUnionSourceMarkedNumerator C R n Q.a V η j h) x
        ∂fullSpatialPatchDesign d n) ≤ (completeSourceCrudeSpatialBase d Chi)^n*η^4*
          (highRowTotalMass R.rowMass+1)^2 := by
  obtain ⟨Cfr0,η0,hfr,hη0,hbound⟩ := completeSourceNumerator_original_field_bound C Q
  refine ⟨Cfr0,η0,hfr,hη0,?_⟩
  intro k D M q n hk0 horder hk hD hq hn hM Cfr lam ℓ N μ cf hCfr hℓ hℓN hcf hη V hV j h
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let η := cf*(k : ℝ)^(-C.smoothness)
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ (hfr.trans hCfr) hℓ hℓN
  exact crude_raw_spatial_response_energy _ η (highRowTotalMass R.rowMass)
    (highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1).le G.total_positive.le
    (highUnionSourceMarkedNumerator C R n Q.a V η j h)
    (highUnionSourceMarkedNumerator_measurable C R G n Q.a V η j h)
    (fun x y => hbound k D M q n hk0 horder hk hD hq hn hM Cfr lam ℓ N μ cf
      hCfr hℓ hℓN hcf hη V hV j h x y)

theorem completeSourceMarkedNumerator_original_factorial_tail {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Csharp : ℝ) (hCs : 0 ≤ Csharp) :
    ∃ Cfr0 η0 : ℝ, 1 ≤ Cfr0 ∧ 0 < η0 ∧
      ∀ k D M q J : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ℓ N μ cf : ℝ, Cfr0 ≤ Cfr → 0 < ℓ → ℓ < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ η0 →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)),
      ∀ occupancy : ℝ, 0 ≤ occupancy → occupancy ≤ 1 →
      let R := completeSourceRows C k D M q Cfr lam ℓ N μ
      let η := cf*(k : ℝ)^(-C.smoothness)
      let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
      let C7 := completeSourceCrudeFactorialConstant d Chi Csharp
      (∑ t ∈ Finset.range J, poissonCountWeight (Csharp*occupancy) (D+1+t) *
        ∫ x, selectedRawSquareEnergy
          (highUnionSourceMarkedNumerator C R (D+1+t) Q.a V η j h) x
          ∂fullSpatialPatchDesign d (D+1+t)) ≤
        C7*η^4*(highRowTotalMass R.rowMass+1)^2*poissonCountWeight (C7*occupancy) (D+1) := by
  obtain ⟨Cfr0,η0,hfr,hη0,hbound⟩ := completeSourceNumerator_original_field_bound C Q
  refine ⟨Cfr0,η0,hfr,hη0,?_⟩
  intro k D M q J hk0 horder hk hD hq hM Cfr lam ℓ N μ cf hCfr hℓ hℓN hcf hη V hV j h occupancy ho ho1
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let η := cf*(k : ℝ)^(-C.smoothness)
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ (hfr.trans hCfr) hℓ hℓN
  apply crude_raw_spatial_factorial_tail d D J _ Csharp η (highRowTotalMass R.rowMass) occupancy
    (highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1).le hCs G.total_positive.le ho ho1
    (fun n => highUnionSourceMarkedNumerator C R n Q.a V η j h)
    (fun n => highUnionSourceMarkedNumerator_measurable C R G n Q.a V η j h)
  intro t _ x y
  exact hbound k D M q (D+1+t) hk0 horder hk hD hq (by omega) hM Cfr lam ℓ N μ cf
    hCfr hℓ hℓN hcf hη V hV j h x y

end NearlyMinimax
