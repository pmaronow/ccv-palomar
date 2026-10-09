module

public import NearlyMinimax.DyadicApproximation
public import NearlyMinimax.IncrementPilotFeatures


@[expose] public section

/-! Joint Borel measurability of the actual anchored charts and pilot fields. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem dyadicNormalizedAnchor_measurable {d : ℕ} (j : ℕ) :
    Measurable (dyadicNormalizedAnchor (d := d) j) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_const.mul ((measurable_pi_apply i).sub
    ((measurable_of_countable (fun c : Fin d → Fin ((2 : ℕ) ^ j) => regularGridCorner ((2 : ℕ) ^ j) c i)).comp
      (regular_grid_cell_measurable _ (by positivity))))

theorem dyadicAnchoredFeature_joint_measurable {d ℓ : ℕ} (j : ℕ) (γ : AnchoredIndex d ℓ) :
    Measurable (fun z : Covariate d × Covariate d => dyadicAnchoredFeature j z.1 z.2 γ) := by
  apply Continuous.measurable
  apply (anchoredMonomial_continuous γ).comp
  apply continuous_pi
  intro i
  exact continuous_const.mul (((continuous_apply i).comp continuous_snd).sub
    ((continuous_apply i).comp continuous_fst))

theorem dyadic_cell_pair_measurable {d : ℕ} (j : ℕ) :
    MeasurableSet {z : Covariate d × Covariate d | z.2 ∈ dyadicPilotCell j z.1} := by
  exact measurableSet_eq_fun ((regular_grid_cell_measurable _ (by positivity)).comp measurable_snd)
    ((regular_grid_cell_measurable _ (by positivity)).comp measurable_fst)

theorem dyadic_cell_integral_measurable {d : ℕ} (j : ℕ) (μ : Measure (Covariate d)) [SFinite μ]
    (f : Covariate d × Covariate d → ℝ) (hf : Measurable f) :
    Measurable (fun x => ∫ z in dyadicPilotCell j x, f (x, z) ∂μ) := by
  let S := {z : Covariate d × Covariate d | z.2 ∈ dyadicPilotCell j z.1}
  have hi := ((hf.indicator (dyadic_cell_pair_measurable j)).stronglyMeasurable.integral_prod_right'
    (ν := μ)).measurable
  convert hi using 1
  funext x
  rw [← integral_indicator (dyadicPilotCell_measurable j x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    by_cases h : z ∈ dyadicPilotCell j x <;> simp [S, h])

theorem matrix_nonsing_inverse_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℝ => A⁻¹) := by
  apply Measurable.of_eval_matrix
  intro i k
  have hd : Measurable (fun A : Matrix ι ι ℝ => A.det) := continuous_id.matrix_det.measurable
  have ha : Measurable (fun A : Matrix ι ι ℝ => A.adjugate i k) :=
    continuous_id.matrix_adjugate.measurable.eval_matrix
  convert hd.inv.mul ha using 1
  funext A
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

theorem dyadicKnownGram_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (dyadicKnownGram (d := d) (ℓ := ℓ) j) := by
  have he : dyadicKnownGram (d := d) (ℓ := ℓ) j =
      anchoredGram ∘ dyadicNormalizedAnchor j := funext (dyadicKnownGram_eq_normalized j)
  rw [he]
  exact anchoredGram_continuous.measurable.comp (dyadicNormalizedAnchor_measurable j)

theorem dyadicKnownGram_inverse_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (fun x : Covariate d => (dyadicKnownGram (ℓ := ℓ) j x)⁻¹) :=
  matrix_nonsing_inverse_measurable.comp (dyadicKnownGram_measurable j)

theorem dyadicPopulationGram_measurable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    Measurable (dyadicPopulationGram (ℓ := ℓ) θ j) := by
  let := designLaw_isProbability C θ hθ
  apply Measurable.of_eval_matrix
  intro γ δ
  exact measurable_const.mul (dyadic_cell_integral_measurable j (designLaw θ) _
    ((dyadicAnchoredFeature_joint_measurable j γ).mul (dyadicAnchoredFeature_joint_measurable j δ)))

theorem dyadicResponseMoment_measurable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    Measurable (dyadicResponseMoment (ℓ := ℓ) θ j) := by
  let := designLaw_isProbability C θ hθ
  apply measurable_pi_iff.mpr
  intro γ
  exact measurable_const.mul (dyadic_cell_integral_measurable j (designLaw θ) _
    ((dyadicAnchoredFeature_joint_measurable j γ).mul (hθ.2.1.comp measurable_snd)))

theorem dyadicConstantMoment_measurable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    Measurable (dyadicConstantMoment (ℓ := ℓ) θ j) := by
  let := designLaw_isProbability C θ hθ
  apply measurable_pi_iff.mpr
  intro γ
  exact measurable_const.mul (dyadic_cell_integral_measurable j (designLaw θ) _
    (dyadicAnchoredFeature_joint_measurable j γ))

theorem dyadicPopulationFit_measurable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    Measurable (dyadicPopulationFit (ℓ := ℓ) θ j) := by
  have hA := matrix_nonsing_inverse_measurable.comp (dyadicPopulationGram_measurable (ℓ := ℓ) C θ hθ j)
  apply measurable_pi_iff.mpr
  intro γ
  exact Finset.measurable_sum Finset.univ (fun δ _ => (hA.eval_matrix (i := γ) (j := δ)).mul
    (((dyadicResponseMoment_measurable C θ hθ j).eval (a := δ)).sub
      (hθ.2.1.mul ((dyadicConstantMoment_measurable C θ hθ j).eval (a := δ)))))

theorem dyadicPilotScalar_joint_measurable {d ℓ : ℕ} (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun v : Covariate d × Observation d => dyadicPilotScalar j v.1 a v.2) := by
  have hpair : Measurable (fun v : Covariate d × Observation d => (v.1, v.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hφ (γ : AnchoredIndex d ℓ) := (dyadicAnchoredFeature_joint_measurable j γ).comp hpair
  cases a with
  | inl a => exact (hφ a.1).mul (hφ a.2)
  | inr a =>
    cases a with
    | inl γ => exact (measurable_snd.comp measurable_snd).mul (hφ γ)
    | inr γ => exact hφ γ

theorem dyadicPilotFeature_joint_measurable {d ℓ : ℕ} (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun v : Covariate d × Observation d => dyadicPilotFeature j v.1 a v.2) := by
  let S := {v : Covariate d × Observation d | v.2.1 ∈ dyadicPilotCell j v.1}
  have hS : MeasurableSet S := (dyadic_cell_pair_measurable j).preimage
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h : Measurable (fun v : Covariate d × Observation d => dyadicPilotScale d j *
      S.indicator (fun v => dyadicPilotScalar j v.1 a v.2) v) :=
    measurable_const.mul ((dyadicPilotScalar_joint_measurable j a).indicator hS)
  convert h using 1
  funext v
  by_cases hv : v.2.1 ∈ dyadicPilotCell j v.1 <;> simp [dyadicPilotFeature, S, hv]

theorem preconditionedPilotFeature_joint_measurable {d ℓ : ℕ} (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun v : Covariate d × Observation d => preconditionedPilotFeature j v.1 a v.2) := by
  unfold preconditionedPilotFeature
  apply Finset.measurable_sum
  intro β _
  exact (((dyadicKnownGram_inverse_measurable j).eval_matrix (i := localPilotRow a) (j := β)).comp
    measurable_fst).mul (dyadicPilotFeature_joint_measurable j (localPilotReplaceRow a β))

theorem dyadicIncrementFeature_joint_measurable {d ℓ : ℕ} (j : ℕ)
    (a : incrementVariables (anchoredDimension d ℓ)) :
    Measurable (fun v : Covariate d × Observation d => dyadicIncrementFeature j v.1 a v.2) := by
  cases a with
  | inl a =>
    cases a with
    | inl a => exact preconditionedPilotFeature_joint_measurable j _
    | inr a =>
      change Measurable (fun v : Covariate d × Observation d => if j = 0 then
        (if a.2.1 = a.2.2 then (1 : ℝ) else 0) else
        preconditionedPilotFeature (j - 1) v.1
          (Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2)) v.2)
      split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable _ _
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    change Measurable (fun v : Covariate d × Observation d => if parent && (j == 0) then (0 : ℝ) else
      preconditionedPilotFeature (if parent then j - 1 else j) v.1
        (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
          else Sum.inr (Sum.inl (anchoredFinIndex i))) v.2)
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable _ _

theorem dyadicIncrementRawVector_joint_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (fun v : Covariate d × Observation d => dyadicIncrementRawVector (ℓ := ℓ) j v.1 v.2) :=
  measurable_pi_iff.mpr (fun _ => dyadicIncrementFeature_joint_measurable j _)

theorem dyadicIncrementRawMean_measurable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    Measurable (dyadicIncrementRawMean (ℓ := ℓ) θ j) := by
  let := observationLaw_isProbability C θ hθ
  apply measurable_pi_iff.mpr
  intro a
  exact (((dyadicIncrementRawVector_joint_measurable (ℓ := ℓ) j).eval (a := a)).stronglyMeasurable.integral_prod_right'
    (ν := observationLaw θ)).measurable

end NearlyMinimax
