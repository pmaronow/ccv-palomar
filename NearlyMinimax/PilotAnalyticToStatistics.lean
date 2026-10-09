module

public import NearlyMinimax.PilotCommonBounds


@[expose] public section

/-! Actual statistical consequences of a genuine population derivative bound.
The endpoint below will discharge its analytic input uniformly over domains. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem dyadicIncrementKernel_raw_budget_of_derivative {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A)
    (hder : ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
        ‖iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
          C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤ (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k) :
    ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ, ∀ hk : k ≤ n,
      ∀ Λ : ℝ, 0 < Λ →
        (((k.factorial : ℝ) * Λ ^ k)⁻¹) *
          (∫ z : Fin n → Observation d,
            dyadicIncrementKernel C θ j x y m row k
              (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2 ∂sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 * (k.factorial : ℝ) *
            (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
              preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ k := by
  intro n j x hx y hy m k row hk Λ hΛ
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := C.order) j x (z i)
  let e := Fin.castLEEmb hk
  let E := (Fintype.card (incrementVariables (anchoredDimension d C.order)) : ℝ) *
    preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j
  have hE : 0 ≤ E := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
      (dyadicPilotScale_pos _ _).le
  have hrow : 0 ≤ (∑ i, |row i|) * D :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le
  have hb := KernelMomentBounds.factorial_kernel_budget
    (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row) (dyadicIncrementRawMean θ j x))
    (fun i => X (e i)) (hind.precomp e.injective) (fun i => hmeas (e i))
    (fun i a => hL2 (e i) a) E ((∑ i, |row i|) * D) A Λ hE hrow hA.le hΛ
    (fun i => dyadicIncrementRawVector_sample_second_le C θ hθ j x hx (e i))
    (hder j x hx y hy m k row)
  have heq : (fun z : Fin n → Observation d =>
      dyadicIncrementKernel C θ j x y m row k
        (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2) =
      (fun z => iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row) (dyadicIncrementRawMean θ j x)
        (fun i => X (e i) z) ^ 2) := by
    funext z
    rw [dyadicIncrementKernel_raw]
  rw [heq]
  exact hb


theorem dyadicPolynomialPilot_variance_of_derivative {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A)
    (hder : ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
        ‖iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
          C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤ (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k) :
    ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
      m + anchoredDimension d C.order + 1 ≤ n →
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
        variance (dyadicPolynomialPilot C n j x y m row) (sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 *
            ∑ t : Fin (m + anchoredDimension d C.order + 1),
              ((t.val + 1).factorial : ℝ) *
                (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
                  preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (t.val + 1) := by
  intro n j x hx y hy m row hdegree Λ hΛ hΛn
  let := sampleLaw_isProbability C θ hθ n
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := C.order) j x (z i)
  let E := (Fintype.card (incrementVariables (anchoredDimension d C.order)) : ℝ) *
    preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j
  have hE : 0 ≤ E := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
      (dyadicPilotScale_pos _ _).le
  have hrow : 0 ≤ (∑ i, |row i|) * D :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  have hv := LiftL2.polynomialLift_variance_le_raw_power_l2 F X (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hind hmeas hid hL2 hmean Λ hΛ
    (by simpa only [Nat.cast_add, Nat.cast_one] using hΛn)
  apply hv.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt t.isLt).trans hdegree)
  have hFeval : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
  have hd : ‖iteratedFDeriv ℝ (t.val + 1) (fun z => eval z F) (dyadicIncrementRawMean θ j x)‖ ≤
      ((∑ i, |row i|) * D) * ((t.val + 1).factorial : ℝ) * A ^ (t.val + 1) := by
    rw [hFeval]
    exact hder j x hx y hy m (t.val + 1) row
  have hb := KernelMomentBounds.factorial_kernel_budget
    (iteratedFDeriv ℝ (t.val + 1) (fun z => eval z F) (dyadicIncrementRawMean θ j x))
    (fun i => X (e i)) (hind.precomp e.injective) (fun i => hmeas (e i))
    (fun i a => hL2 (e i) a) E ((∑ i, |row i|) * D) A Λ hE hrow hA.le hΛ
    (fun i => dyadicIncrementRawVector_sample_second_le C θ hθ j x hx (e i)) hd
  simpa only [E, e, mul_assoc] using hb


theorem dyadicPilotErrorField_test_variance_of_raw_budget {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A)
    (hraw : ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ, ∀ hk : k ≤ n,
      ∀ Λ : ℝ, 0 < Λ →
        (((k.factorial : ℝ) * Λ ^ k)⁻¹) *
          (∫ z : Fin n → Observation d,
            dyadicIncrementKernel C θ j x y m row k
              (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2 ∂sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 * (k.factorial : ℝ) *
            (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
              preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ k) :
    ∀ n j J : ℕ, j ≤ J →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      m + anchoredDimension d C.order + 1 ≤ n →
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
      ∀ ν : Covariate d × Covariate d → ℝ,
      MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) →
      variance (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
        ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) (sampleLaw θ n) ≤
      (C.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) *
        ((dyadicPilotRowCap d C.order j J * D) ^ 2 *
          ∑ r : Fin (m + anchoredDimension d C.order + 1),
            ((r.val + 1).factorial : ℝ) *
              (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
                preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (r.val + 1)) *
        (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) := by
  intro n j J hj y hy m hdegree Λ hΛ hΛn ν hν
  let := sampleLaw_isProbability C θ hθ n
  let M := regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)
  let := regularPairDesignMeasure_isFinite C θ hθ ((2 : ℕ) ^ J) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let X (i : Fin n) (z : Fin n → Observation d) := incrementGlobalVector (ℓ := C.order) j (z i)
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  let rowcap := dyadicPilotRowCap d C.order j J
  have hrowcap : 0 ≤ rowcap := dyadicPilotRowCap_nonneg _ _ _ _
  have hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d :=
    (regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity)).mono (fun w hw => hw.1)
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j J hj
  have hHmeas (r : Fin R) : AEStronglyMeasurable (fun w => H w r) M :=
    (dyadicIncrementKernel_field_measurable C θ hθ j y m (r.val + 1) _
      (dyadicPilotRow_field_measurable j)).aestronglyMeasurable
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M rowcap hrowcap hcube hrow ν hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  let e (r : Fin R) := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hdegree)
  let Op (r : Fin R) := FieldLiftCovariance.rawKernelOperator (e r) X hind hmeas hL2
  have hcaps (r : Fin R) : ∃ B : ℝ, 0 < B ∧ ∀ᵐ w ∂M, ‖H w r‖ ≤ B :=
    dyadicIncrementKernel_field_norm_bound C θ hθ j y hy m (r.val + 1) _ M rowcap hrowcap hcube hrow
  let B (r : Fin R) := Classical.choose (hcaps r)
  have hBpos (r : Fin R) : 0 < B r := (Classical.choose_spec (hcaps r)).1
  have hBcap (r : Fin R) : ∀ᵐ w ∂M, ‖H w r‖ ≤ B r := (Classical.choose_spec (hcaps r)).2
  have hopcap (r : Fin R) : ∀ᵐ w ∂M, ‖Op r (H w r)‖ ≤ ‖Op r‖ * B r := by
    filter_upwards [hBcap r] with w hw
    exact ((Op r).le_opNorm _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  have hblock (c : Fin (Fintype.card (DyadicPilotLabelIndex d (j - 1)))) :
      M.real {w | dyadicPilotLabel (j - 1) w.1 = c} ≤ C.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
    have hs : {w : Covariate d × Covariate d | dyadicPilotLabel (j - 1) w.1 = c} =
        {w | regularGridCell ((2 : ℕ) ^ (j - 1)) (by positivity) w.1 =
          (Fintype.equivFin (DyadicPilotLabelIndex d (j - 1))).symm c} := by
      ext w
      exact (Fintype.equivFin (DyadicPilotLabelIndex d (j - 1))).apply_eq_iff_eq_symm_apply
    rw [hs]
    exact regularPairDesignMeasure_parent_block_mass C θ hθ ((2 : ℕ) ^ J) (by positivity) j _
  have hu := FieldLiftCovariance.integrated_centered_lift_variance_localized
    (μ := sampleLaw θ n) (M := M) (n := n)
    (p := Fintype.card (IncrementGlobalIndex d C.order j)) (R := R)
    (q := Fintype.card (DyadicPilotLabelIndex d (j - 1))) H ν hν hH hHmeas
    (fun w r σ v => dyadicIncrementKernel_symmetric C θ j w.1 y m (dyadicPilotRow j w.1 w.2) _ σ v)
    X (incrementGlobalMean θ j) hdegree hind hmeas hid hL2 hmean Λ hΛ
    (by simpa only [R, Nat.cast_add, Nat.cast_one] using hΛn)
    (fun w => dyadicPilotLabel (j - 1) w.1) ((dyadicPilotLabel_measurable _).comp measurable_fst)
    (fun r => ‖Op r‖ * B r) (fun r => mul_nonneg (norm_nonneg (Op r)) (hBpos r).le) hopcap
    (fun r w v hv => Filter.Eventually.of_forall (fun z =>
      dyadicIncrementKernel_disjoint C θ j (r.val + 1) (by omega) w.1 v.1 hv y y m m
        (dyadicPilotRow j w.1 w.2) (dyadicPilotRow j v.1 v.2) (fun i => z (e r i))))
    (C.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) hblock
  let δ (r : Fin R) := (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹
  let S (w : Covariate d × Covariate d) := ∑ r : Fin R, δ r * ‖Op r (H w r)‖ ^ 2
  let P := (rowcap * D) ^ 2 * ∑ r : Fin R, ((r.val + 1).factorial : ℝ) *
    (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
      preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (r.val + 1)
  have hSmeas : AEStronglyMeasurable S M := by
    have hm : AEStronglyMeasurable (∑ r : Fin R, fun w => δ r * ‖Op r (H w r)‖ ^ 2) M :=
      Finset.aestronglyMeasurable_sum Finset.univ (fun r _ =>
        ((Op r).continuous.comp_aestronglyMeasurable (hHmeas r)).norm.pow 2 |>.const_mul (δ r))
    convert hm using 1
    funext w
    simp only [S, Finset.sum_apply]
  have hSnon (w) : 0 ≤ S w := Finset.sum_nonneg (fun r _ => mul_nonneg (by dsimp [δ]; positivity) (sq_nonneg _))
  have hSbound : ∀ᵐ w ∂M, S w ≤ P := by
    filter_upwards [hcube, hrow] with w hw hr
    unfold S P
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have hb := hraw n j w.1 hw y hy m (r.val + 1) (dyadicPilotRow j w.1 w.2)
      ((Nat.succ_le_of_lt r.isLt).trans hdegree) Λ hΛ
    have he : ‖Op r (H w r)‖ ^ 2 = ∫ z : Fin n → Observation d,
        H w r (fun i => X (e r i) z) ^ 2 ∂sampleLaw θ n :=
      FieldLiftCovariance.raw_kernel_operator_norm_sq (e r) X hind hmeas hL2 (H w r)
    rw [he]
    apply hb.trans
    have hprod : 0 ≤ A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
        preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ := by
      have hc := preconditionedPilotMomentConstant_pos C C.order
      have hk := dyadicPilotScale_pos d j
      positivity
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hprod _))
    apply pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le)
    exact mul_le_mul_of_nonneg_right hr hD.le
  have hStop : MemLp S ∞ M := memLp_top_of_bound hSmeas P (hSbound.mono (fun w hw => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hSnon w)]
    exact hw))
  have hi : Integrable (fun w => ν w ^ 2 * S w) M := by
    convert hν.integrable_sq.mul_of_top_right hStop using 1
    funext w
    simp only [Pi.mul_apply]
    exact mul_comm _ _
  have hile := integral_mono_ae hi (hν.integrable_sq.const_mul P)
    (hSbound.mono (fun w hw => (mul_le_mul_of_nonneg_left hw (sq_nonneg (ν w))).trans_eq (mul_comm _ _)))
  rw [integral_const_mul] at hile
  have hrhs : (∫ w, ν w ^ 2 * ∑ r : Fin R, δ r *
      ∫ z : Fin n → Observation d, H w r (fun i => X (e r i) z) ^ 2 ∂sampleLaw θ n ∂M) =
      ∫ w, ν w ^ 2 * S w ∂M := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by
      apply congrArg (fun a => ν w ^ 2 * a)
      apply Finset.sum_congr rfl
      intro r _
      rw [← FieldLiftCovariance.raw_kernel_operator_norm_sq (e r) X hind hmeas hL2 (H w r)]
  have herr : (fun z : Fin n → Observation d => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w) (fun i z => X i z - incrementGlobalMean θ j) z ∂M) =
      (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w ∂M) := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
      (dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree z)
  rw [herr, hrhs] at hu
  exact hu.trans (by
    have hL : 0 ≤ C.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
      exact div_nonneg (sq_nonneg _) (dyadicPilotScale_pos _ _).le
    simpa only [P, R, rowcap, mul_assoc] using mul_le_mul_of_nonneg_left hile hL)


end NearlyMinimax
