module

public import NearlyMinimax.IncrementPilotCoordinates
public import NearlyMinimax.AnchoredCoefficientBounds
public import NearlyMinimax.DyadicMeasurability


@[expose] public section

/-! Actual measurable finite coordinate fields and fixed-level bounds.
These bounds establish Bochner integrability; sharp level dependence is obtained
from the separate original-law pilot energy estimates. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem dyadicPilotCoordinate_measurable {d ℓ : ℕ} (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun x : Covariate d => dyadicPilotCoordinate j x a) := by
  have hlin : Measurable (fun x : Covariate d => pilotPolynomialLinear (ℓ := 2 * ℓ)
      (dyadicPilotLabel j x) (dyadicPilotPolynomial j x a) (dyadicPilotResponse a)) := by
    unfold pilotPolynomialLinear
    apply Finset.measurable_sum
    intro β _
    exact (dyadicPilotPolynomial_coeff_continuous j a _).measurable.smul
      ((measurable_of_countable (fun c : Fin (Fintype.card (DyadicPilotLabelIndex d j)) =>
        (ContinuousLinearMap.proj ((Fintype.equivFin
          (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ)))
            ((c, β), dyadicPilotResponse a)) :
          (Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ))).comp (dyadicPilotLabel_measurable j))
  exact (measurable_const : Measurable (fun _ : Covariate d => dyadicPilotScale d j)).smul hlin

theorem preconditionedPilotCoordinate_measurable {d ℓ : ℕ} (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun x : Covariate d => preconditionedPilotCoordinate j x a) := by
  unfold preconditionedPilotCoordinate
  exact Finset.measurable_sum Finset.univ (fun β _ =>
    ((dyadicKnownGram_inverse_measurable j).eval_matrix (i := localPilotRow a) (j := β)).smul
      (dyadicPilotCoordinate_measurable j (localPilotReplaceRow a β)))

theorem incrementPilotFreeCoordinate_measurable {d ℓ : ℕ} (j : ℕ)
    (a : incrementVariables (anchoredDimension d ℓ)) :
    Measurable (fun x : Covariate d => incrementPilotFreeCoordinate j x a) := by
  let pc : ((Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalCurrent j)
  let pp : ((Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalParent j)
  have hc (a : LocalPilotIndex d ℓ) : Measurable (fun x : Covariate d =>
      (preconditionedPilotCoordinate j x a).comp (incrementGlobalCurrent j)) :=
    pc.measurable.comp
      (preconditionedPilotCoordinate_measurable j a)
  have hp (a : LocalPilotIndex d ℓ) : Measurable (fun x : Covariate d =>
      (preconditionedPilotCoordinate (j - 1) x a).comp (incrementGlobalParent j)) :=
    pp.measurable.comp
      (preconditionedPilotCoordinate_measurable (j - 1) a)
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      change Measurable (fun x : Covariate d => if j = 0 then
        (if a.2.1 = a.2.2 then incrementGlobalOne j else 0) else _)
      split_ifs
      · exact measurable_const
      · exact measurable_const
      · exact hp (Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2))
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp only [incrementPilotFreeCoordinate]
    split_ifs
    · exact measurable_const
    · exact hp (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hp (Sum.inr (Sum.inl (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inl (anchoredFinIndex i)))

theorem incrementPilotCoordinate_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (incrementPilotCoordinate (d := d) (ℓ := ℓ) j) := by
  exact (ContinuousLinearMap.piEquivL ℝ
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ)
    (fun _ : Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) => ℝ)).continuous.measurable.comp
      (measurable_pi_iff.mpr (fun _ => incrementPilotFreeCoordinate_measurable j _))

theorem real_pi_projection_norm_le {ι : Type*} [Fintype ι] (i : ι) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v i

theorem pilotPolynomialLinear_norm_le {q d ℓ : ℕ} (c : Fin q)
    (P : MvPolynomial (Fin d) ℝ) (response : Bool) (M : ℝ) (hM : 0 ≤ M)
    (hP : ∀ β : PolynomialBox d ℓ, |P.coeff (polynomialBoxExponent β)| ≤ M) :
    ‖pilotPolynomialLinear (ℓ := ℓ) c P response‖ ≤
      (Fintype.card (PolynomialBox d ℓ) : ℝ) * M := by
  apply (norm_sum_le _ _).trans
  calc
    (∑ β : PolynomialBox d ℓ, ‖P.coeff (polynomialBoxExponent β) •
      (ContinuousLinearMap.proj ((Fintype.equivFin (PilotBasisIndex q d ℓ)) ((c, β), response)) :
        (Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ) →L[ℝ] ℝ)‖) ≤ ∑ _β : PolynomialBox d ℓ, M := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hP β) (real_pi_projection_norm_le _) (norm_nonneg _) hM).trans_eq (mul_one M)
    _ = (Fintype.card (PolynomialBox d ℓ) : ℝ) * M := by simp

theorem dyadicPilotCoordinate_uniform_bound {d ℓ : ℕ} (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ‖dyadicPilotCoordinate j x a‖ ≤ M := by
  obtain ⟨P, hP, hcap⟩ := dyadicPilotPolynomial_coeff_uniform_bound (d := d) (ℓ := ℓ) j
  let B := dyadicPilotScale d j * ((Fintype.card (PolynomialBox d (2 * ℓ)) : ℝ) * P)
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx a
  have hscale : 0 ≤ dyadicPilotScale d j := by dsimp [dyadicPilotScale]; positivity
  rw [dyadicPilotCoordinate, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  exact (mul_le_mul_of_nonneg_left (pilotPolynomialLinear_norm_le _ _ _ P hP.le
    (hcap x hx a)) hscale).trans (le_max_right _ _)

theorem preconditionedPilotCoordinate_uniform_bound {d ℓ : ℕ} (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ‖preconditionedPilotCoordinate j x a‖ ≤ M := by
  obtain ⟨L, hL, hLb⟩ := dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
  obtain ⟨P, hP, hPb⟩ := dyadicPilotCoordinate_uniform_bound (d := d) (ℓ := ℓ) j
  let B := (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (L * P)
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx a
  letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
  unfold preconditionedPilotCoordinate
  apply (norm_sum_le _ _).trans
  calc
    (∑ β : AnchoredIndex d ℓ, ‖(dyadicKnownGram j x)⁻¹ (localPilotRow a) β •
        dyadicPilotCoordinate j x (localPilotReplaceRow a β)‖) ≤ ∑ _β : AnchoredIndex d ℓ, L * P := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul]
      exact mul_le_mul ((matrix_real_entry_norm_le _ _ _).trans (hLb j x hx))
        (hPb x hx _) (norm_nonneg _) hL.le
    _ = B := by simp [B]
    _ ≤ max 1 B := le_max_right _ _

theorem incrementGlobalCurrent_norm_le {d ℓ : ℕ} (j : ℕ) :
    ‖incrementGlobalCurrent (d := d) (ℓ := ℓ) j‖ ≤ 1 :=
  ContinuousLinearMap.norm_pi_le_of_le (fun _ => real_pi_projection_norm_le _) zero_le_one

theorem incrementGlobalParent_norm_le {d ℓ : ℕ} (j : ℕ) :
    ‖incrementGlobalParent (d := d) (ℓ := ℓ) j‖ ≤ 1 :=
  ContinuousLinearMap.norm_pi_le_of_le (fun _ => real_pi_projection_norm_le _) zero_le_one

theorem incrementPilotCoordinate_uniform_bound {d ℓ : ℕ} (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ‖incrementPilotCoordinate (ℓ := ℓ) j x‖ ≤ M := by
  obtain ⟨C, hC, hCb⟩ := preconditionedPilotCoordinate_uniform_bound (d := d) (ℓ := ℓ) j
  obtain ⟨P, hP, hPb⟩ := preconditionedPilotCoordinate_uniform_bound (d := d) (ℓ := ℓ) (j - 1)
  let M := max 1 (max C P)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hCM : C ≤ M := (le_max_left C P).trans (le_max_right 1 (max C P))
  have hPM : P ≤ M := (le_max_right C P).trans (le_max_right 1 (max C P))
  have hOne : ‖incrementGlobalOne (d := d) (ℓ := ℓ) j‖ ≤ 1 := real_pi_projection_norm_le _
  have hc (a : LocalPilotIndex d ℓ) :
      ‖(preconditionedPilotCoordinate j x a).comp (incrementGlobalCurrent j)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hCb x hx a) (incrementGlobalCurrent_norm_le j) (norm_nonneg _) hC.le).trans
        (by simpa only [mul_one] using hCM))
  have hp (a : LocalPilotIndex d ℓ) :
      ‖(preconditionedPilotCoordinate (j - 1) x a).comp (incrementGlobalParent j)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hPb x hx a) (incrementGlobalParent_norm_le j) (norm_nonneg _) hP.le).trans
        (by simpa only [mul_one] using hPM))
  apply ContinuousLinearMap.norm_pi_le_of_le _ hM.le
  intro i
  let a := (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm i
  change ‖incrementPilotFreeCoordinate j x a‖ ≤ M
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      simp only [incrementPilotFreeCoordinate]
      split_ifs
      · exact hOne.trans (le_max_left _ _)
      · simpa only [norm_zero] using hM.le
      · exact hp (Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2))
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp only [incrementPilotFreeCoordinate]
    split_ifs
    · simpa only [norm_zero] using hM.le
    · exact hp (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hp (Sum.inr (Sum.inl (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inl (anchoredFinIndex i)))

end NearlyMinimax
