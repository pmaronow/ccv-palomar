module

public import NearlyMinimax.IncrementKernelMeasurability
public import NearlyMinimax.DyadicPilotRows
public import NearlyMinimax.BoundedPairMeanOperators


@[expose] public section

/-! Actual universal-test covariance for the dyadic polynomial pilot under
the paper's original weighted same-cell pair measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

theorem dyadicPilotRow_field_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (fun w : Covariate d × Covariate d => dyadicPilotRow (ℓ := ℓ) j w.1 w.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((anchoredMonomial_continuous (anchoredFinIndex i)).comp
    (continuous_pi (fun t => continuous_const.mul
      (((continuous_apply t).comp continuous_snd).sub
        ((continuous_apply t).comp continuous_fst))))).measurable

theorem regularPairDesignMeasure_same_cell_ae {d : ℕ} (θ : RegressionParameter d)
    (k : ℕ) (hk : 0 < k) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, regularGridCell k hk w.1 = regularGridCell k hk w.2 := by
  unfold regularPairDesignMeasure
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (measurableSet_eq_fun
    ((regular_grid_cell_measurable k hk).comp measurable_fst)
    ((regular_grid_cell_measurable k hk).comp measurable_snd))

def dyadicPilotRowCap (d ℓ j J : ℕ) : ℝ :=
  (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹

theorem dyadicPilotRowCap_nonneg (d ℓ j J : ℕ) : 0 ≤ dyadicPilotRowCap d ℓ j J := by
  unfold dyadicPilotRowCap
  positivity

theorem dyadicPilotRow_pair_cap {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j J : ℕ) (hj : j ≤ J) :
    ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity),
      (∑ i, |dyadicPilotRow (ℓ := ℓ) j w.1 w.2 i|) ≤ dyadicPilotRowCap d ℓ j J := by
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity),
    regularPairDesignMeasure_same_cell_ae θ ((2 : ℕ) ^ J) (by positivity)] with w hw hc
  exact dyadicPilotRow_sum_abs_le_fine_cell j J hj w.1 w.2 hw.1 hw.2 hc.symm

def dyadicPilotErrorField {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (n j : ℕ) (y : ℝ) (m : ℕ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  dyadicPolynomialPilot C n j w.1 y m (dyadicPilotRow j w.1 w.2) z -
    incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m (dyadicPilotRow j w.1 w.2)
        (dyadicIncrementRawMean θ j w.1)

/-- Every L² test of the actual centered pilot error is truly L² and has
mean zero under the original sample law. -/
theorem dyadicPilotErrorField_test_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j J : ℕ) (hj : j ≤ J) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity))) :
    MemLp (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ z, ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  let M := regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)
  let := regularPairDesignMeasure_isFinite C θ hθ ((2 : ℕ) ^ J) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  have hc : ∀ᵐ w ∂M, w.1 ∈ unitCube d :=
    (regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity)).mono (fun w hw => hw.1)
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j J hj
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j J)
      (dyadicPilotRowCap_nonneg _ _ _ _) hc hrow ν hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  have h := FieldLiftCovariance.integrated_centered_lift_moment_facts H ν hH
    (fun i (z : Fin n → Observation d) => incrementGlobalVector j (z i))
    (incrementGlobalMean θ j) hind hmeas hid hL2 hmean
  have heq : (fun z : Fin n → Observation d => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w)
        (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z ∂M) =
      (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w ∂M) := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
      (dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree z)
  rwa [heq] at h

/-- The original U7 universal-test bound for the actual coefficient pilot,
with every raw energy, support block, and population derivative supplied by
the original admissible model. The only test hypothesis is its L² norm. -/
theorem admissible_dyadicPilotErrorField_test_variance {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ n j J : ℕ, j ≤ J →
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
  obtain ⟨D, A, hD, hA, hraw⟩ := admissible_dyadicIncrementKernel_raw_budget C
  refine ⟨D, A, hD, hA, ?_⟩
  intro θ hθ n j J hj y hy m hdegree Λ hΛ hΛn ν hν
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
    have hb := hraw θ hθ n j w.1 hw y hy m (r.val + 1) (dyadicPilotRow j w.1 w.2)
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
