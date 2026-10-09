module

public import NearlyMinimax.DyadicPilotPointwise


@[expose] public section

/-! One fixed finite original-observation feature vector realizes every
anchor-dependent current/parent pilot input as a continuous linear image.
The deterministic root parent is realized by an explicit constant coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev DyadicGlobalDimension (d ℓ j : ℕ) :=
  Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))

abbrev IncrementGlobalIndex (d ℓ j : ℕ) :=
  Unit ⊕ (Fin (DyadicGlobalDimension d ℓ j) ⊕ Fin (DyadicGlobalDimension d ℓ (j - 1)))

def incrementGlobalFeature {d ℓ : ℕ} (j : ℕ) (a : IncrementGlobalIndex d ℓ j)
    (z : Observation d) : ℝ :=
  match a with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z i
  | Sum.inr (Sum.inr i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z i

def incrementGlobalVector {d ℓ : ℕ} (j : ℕ) (z : Observation d) :
    Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ :=
  fun a => incrementGlobalFeature j ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm a) z

def incrementGlobalMean {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) :
    Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ :=
  fun a => ∫ z, incrementGlobalVector (ℓ := ℓ) j z a ∂observationLaw θ

theorem incrementGlobalFeature_measurable {d ℓ : ℕ} (j : ℕ)
    (a : IncrementGlobalIndex d ℓ j) : Measurable (incrementGlobalFeature j a) := by
  cases a with
  | inl _ => exact measurable_const
  | inr a =>
    cases a <;> exact pilotBasisFeature_measurable _ (dyadicPilotLabel_measurable _) _

theorem incrementGlobalVector_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (incrementGlobalVector (d := d) (ℓ := ℓ) j) :=
  measurable_pi_iff.mpr (fun _ => incrementGlobalFeature_measurable j _)

theorem incrementGlobalFeature_memLp_two {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (a : IncrementGlobalIndex d ℓ j) : MemLp (incrementGlobalFeature j a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  cases a with
  | inl _ => exact memLp_const _
  | inr a =>
    cases a <;> exact pilotBasisFeature_memLp_two C θ hθ _ (dyadicPilotLabel_measurable _) _

def incrementGlobalCurrent {d ℓ : ℕ} (j : ℕ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (DyadicGlobalDimension d ℓ j) → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inl i))))

def incrementGlobalParent {d ℓ : ℕ} (j : ℕ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inr i))))

def incrementGlobalOne {d ℓ : ℕ} (j : ℕ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inl ()))

@[simp] theorem incrementGlobalCurrent_raw {d ℓ : ℕ} (j : ℕ) (z : Observation d) :
    incrementGlobalCurrent (ℓ := ℓ) j (incrementGlobalVector j z) =
      pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z := by
  funext i
  simp [incrementGlobalCurrent, incrementGlobalVector, incrementGlobalFeature]

@[simp] theorem incrementGlobalParent_raw {d ℓ : ℕ} (j : ℕ) (z : Observation d) :
    incrementGlobalParent (ℓ := ℓ) j (incrementGlobalVector j z) =
      pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z := by
  funext i
  simp [incrementGlobalParent, incrementGlobalVector, incrementGlobalFeature]

@[simp] theorem incrementGlobalOne_raw {d ℓ : ℕ} (j : ℕ) (z : Observation d) :
    incrementGlobalOne (ℓ := ℓ) j (incrementGlobalVector j z) = 1 := by
  simp [incrementGlobalOne, incrementGlobalVector, incrementGlobalFeature]

def preconditionedPilotCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : (Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ :=
  ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β •
    dyadicPilotCoordinate j x (localPilotReplaceRow a β)

@[simp] theorem preconditionedPilotCoordinate_raw {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) :
    preconditionedPilotCoordinate j x a (pilotRawVector (dyadicPilotLabel j) z) =
      preconditionedPilotFeature j x a z := by
  simp [preconditionedPilotCoordinate, preconditionedPilotFeature, smul_eq_mul,
    dyadicPilotCoordinate_raw_apply]

def incrementPilotFreeCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : incrementVariables (anchoredDimension d ℓ)) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ :=
  match a with
  | Sum.inl (Sum.inl it) =>
    (preconditionedPilotCoordinate j x (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2))).comp
      (incrementGlobalCurrent j)
  | Sum.inl (Sum.inr it) =>
    if j = 0 then (if it.2.1 = it.2.2 then incrementGlobalOne j else 0) else
      (preconditionedPilotCoordinate (j - 1) x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2))).comp
        (incrementGlobalParent j)
  | Sum.inr pri =>
    if pri.1 && (j == 0) then 0 else
      if pri.1 then
        (preconditionedPilotCoordinate (j - 1) x
          (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
            else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2)))).comp (incrementGlobalParent j)
      else
        (preconditionedPilotCoordinate j x
          (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
            else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2)))).comp (incrementGlobalCurrent j)

def incrementPilotCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) :=
  ContinuousLinearMap.pi (fun a => incrementPilotFreeCoordinate j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a))

theorem incrementPilotFreeCoordinate_raw {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : incrementVariables (anchoredDimension d ℓ)) (z : Observation d) :
    incrementPilotFreeCoordinate j x a (incrementGlobalVector j z) = dyadicIncrementFeature j x a z := by
  cases a with
  | inl a =>
    cases a with
    | inl a =>
      rcases a with ⟨i, t⟩
      simp [incrementPilotFreeCoordinate, dyadicIncrementFeature]
    | inr a =>
      by_cases hj : j = 0
      · by_cases hit : a.2.1 = a.2.2 <;> simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj, hit]
      · simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    cases parent <;> cases response <;> by_cases hj : j = 0
    all_goals simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]

@[simp] theorem incrementPilotCoordinate_raw {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (z : Observation d) :
    incrementPilotCoordinate j x (incrementGlobalVector j z) = dyadicIncrementRawVector (ℓ := ℓ) j x z := by
  funext a
  exact incrementPilotFreeCoordinate_raw j x _ z

/-- Actual original-law population integration commutes with the exact
global-coordinate map. This is the common mean needed by field covariance. -/
theorem incrementPilotCoordinate_mean {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    incrementPilotCoordinate (ℓ := ℓ) j x (incrementGlobalMean θ j) = dyadicIncrementRawMean θ j x := by
  let := observationLaw_isProbability C θ hθ
  have hlp := KernelMomentBounds.vector_memLp_two (incrementGlobalVector (ℓ := ℓ) j)
    (incrementGlobalVector_measurable j) (fun a => incrementGlobalFeature_memLp_two C θ hθ j _)
  have hi := hlp.integrable (by norm_num)
  have hm : (∫ z, incrementGlobalVector (ℓ := ℓ) j z ∂observationLaw θ) = incrementGlobalMean θ j := by
    funext a
    exact ((ContinuousLinearMap.proj a :
      (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm
  rw [← hm, ← (incrementPilotCoordinate (ℓ := ℓ) j x).integral_comp_comm hi]
  simp only [incrementPilotCoordinate_raw]
  funext a
  simpa only [ContinuousLinearMap.proj_apply, incrementPilotCoordinate_raw,
    dyadicIncrementRawMean] using ((ContinuousLinearMap.proj a :
    (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) →L[ℝ] ℝ).integral_comp_comm
    ((incrementPilotCoordinate (ℓ := ℓ) j x).integrable_comp hi)).symm

theorem incrementGlobalVector_sample_facts {d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    iIndepFun (fun i (z : Fin n → Observation d) => incrementGlobalVector (ℓ := ℓ) j (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i))) ∧
    (∀ i t : Fin n, IdentDistrib
      (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i))
      (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, incrementGlobalVector (ℓ := ℓ) j (z i) a ∂sampleLaw θ n) =
      incrementGlobalMean θ j a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := incrementGlobalVector_measurable (d := d) (ℓ := ℓ) j
  have hp (i : Fin n) : MeasurePreserving (fun z : Fin n → Observation d => z i)
      (sampleLaw θ n) (observationLaw θ) := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi (fun _ : Fin n => hm.aemeasurable),
    fun i => hm.comp (measurable_pi_apply i), ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib (fun z : Fin n → Observation d => z i)
        (fun z : Fin n → Observation d => z t) (sampleLaw θ n) (sampleLaw θ n) :=
      ⟨(hp i).aemeasurable, (hp t).aemeasurable, (hp i).map_eq.trans (hp t).map_eq.symm⟩
    exact ht.comp hm
  · intro i a
    exact (incrementGlobalFeature_memLp_two C θ hθ j _).comp_measurePreserving (hp i)
  · intro i a
    exact integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i)
      ((incrementGlobalFeature_measurable j
        ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm a)).aestronglyMeasurable)

end NearlyMinimax
