module

public import NearlyMinimax.PreconditionedPilot
public import NearlyMinimax.DyadicNesting


@[expose] public section

/-! The exact current/parent free-moment input of the determinant-cleared
increment polynomial, including the virtual identity parent at level zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def anchoredFinIndex {d ℓ : ℕ} (i : Fin (anchoredDimension d ℓ)) : AnchoredIndex d ℓ :=
  (Fintype.equivFin (AnchoredIndex d ℓ)).symm i

def dyadicIncrementFeature {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (v : incrementVariables (anchoredDimension d ℓ)) (z : Observation d) : ℝ :=
  match v with
  | Sum.inl m => match m with
    | Sum.inl it =>
      preconditionedPilotFeature j x (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2)) z
    | Sum.inr it =>
      if j = 0 then (if it.2.1 = it.2.2 then 1 else 0) else
        preconditionedPilotFeature (j - 1) x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2)) z
  | Sum.inr pri =>
    if pri.1 && (j == 0) then 0 else
      preconditionedPilotFeature (if pri.1 then j - 1 else j) x
        (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
          else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2))) z

def dyadicIncrementRawVector {d ℓ : ℕ} (j : ℕ) (x : Covariate d) (z : Observation d) :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => dyadicIncrementFeature j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) z

def dyadicIncrementRawMean {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => ∫ z, dyadicIncrementRawVector j x z a ∂observationLaw θ

theorem dyadicPilotScale_parent_le (d j : ℕ) : dyadicPilotScale d (j - 1) ≤ dyadicPilotScale d j := by
  unfold dyadicPilotScale
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)) d

theorem dyadicIncrementFeature_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (v : incrementVariables (anchoredDimension d ℓ)) : Measurable (dyadicIncrementFeature j x v) := by
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      exact preconditionedPilotFeature_measurable j x _
    | inr v =>
      change Measurable (fun z : Observation d => if j = 0 then
        (if v.2.1 = v.2.2 then (1 : ℝ) else 0) else
        preconditionedPilotFeature (j - 1) x
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z)
      split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_measurable _ x _
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    change Measurable (fun z : Observation d => if parent && (j == 0) then (0 : ℝ) else
      preconditionedPilotFeature (if parent then j - 1 else j) x
        (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
          else Sum.inr (Sum.inl (anchoredFinIndex i))) z)
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_measurable _ x _

theorem dyadicIncrementRawVector_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    Measurable (dyadicIncrementRawVector (ℓ := ℓ) j x) :=
  measurable_pi_iff.mpr (fun _ => dyadicIncrementFeature_measurable j x _)

theorem dyadicIncrementFeature_memLp_two {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (v : incrementVariables (anchoredDimension d ℓ)) :
    MemLp (dyadicIncrementFeature j x v) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      exact preconditionedPilotFeature_memLp_two C θ hθ j x hx _
    | inr v =>
      change MemLp (fun z : Observation d => if j = 0 then
        (if v.2.1 = v.2.2 then (1 : ℝ) else 0) else
        preconditionedPilotFeature (j - 1) x
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z) 2 (observationLaw θ)
      split_ifs <;> first | exact memLp_const _ | exact preconditionedPilotFeature_memLp_two C θ hθ _ x hx _
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    change MemLp (fun z : Observation d => if parent && (j == 0) then (0 : ℝ) else
      preconditionedPilotFeature (if parent then j - 1 else j) x
        (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
          else Sum.inr (Sum.inl (anchoredFinIndex i))) z) 2 (observationLaw θ)
    split_ifs <;> first | exact memLp_const _ | exact preconditionedPilotFeature_memLp_two C θ hθ _ x hx _

/-- Original-law moment bound for every current/parent free coordinate;
the level-zero identity parent is covered by the same fixed constant. -/
theorem dyadicIncrementFeature_second_le {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (v : incrementVariables (anchoredDimension d ℓ)) :
    (∫ z, dyadicIncrementFeature j x v z ^ 2 ∂observationLaw θ) ≤
      preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  have hC := preconditionedPilotMomentConstant_pos C ℓ
  have hroot : 1 ≤ preconditionedPilotMomentConstant C ℓ := le_max_left _ _
  have hK : 1 ≤ dyadicPilotScale d j := by
    unfold dyadicPilotScale
    exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hnon : 0 ≤ preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j :=
    mul_nonneg hC.le (dyadicPilotScale_pos d j).le
  have hparent (a : LocalPilotIndex d ℓ) :=
    (preconditionedPilotFeature_uniform_second_le C θ hθ (j - 1) x hx a).trans
      (mul_le_mul_of_nonneg_left (dyadicPilotScale_parent_le d j) hC.le)
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      exact preconditionedPilotFeature_uniform_second_le C θ hθ j x hx _
    | inr v =>
      dsimp only [dyadicIncrementFeature]
      split_ifs <;> first
        | simpa using (mul_le_mul hroot hK (by norm_num : (0 : ℝ) ≤ 1) hC.le)
        | simpa using hnon
        | exact hparent _
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent with
    | false =>
      cases response
      all_goals first
        | simpa [dyadicIncrementFeature] using preconditionedPilotFeature_uniform_second_le C θ hθ j x hx
            (Sum.inr (Sum.inl (anchoredFinIndex i)))
        | simpa [dyadicIncrementFeature] using preconditionedPilotFeature_uniform_second_le C θ hθ j x hx
            (Sum.inr (Sum.inr (anchoredFinIndex i)))
    | true =>
      cases response <;> by_cases hj : j = 0
      all_goals first
        | simpa [dyadicIncrementFeature, hj] using hnon
        | simpa [dyadicIncrementFeature, hj] using hparent
            (Sum.inr (Sum.inl (anchoredFinIndex i)))
        | simpa [dyadicIncrementFeature, hj] using hparent
            (Sum.inr (Sum.inr (anchoredFinIndex i)))

theorem dyadicIncrementRawVector_second_le {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    (∫ z, ‖dyadicIncrementRawVector (ℓ := ℓ) j x z‖ ^ 2 ∂observationLaw θ) ≤
      Fintype.card (incrementVariables (anchoredDimension d ℓ)) *
        preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  apply (KernelMomentBounds.vector_second_le_sum_coordinates (dyadicIncrementRawVector j x)
    (dyadicIncrementRawVector_measurable j x) (fun _ => dyadicIncrementFeature_memLp_two C θ hθ j x hx _)).trans
  exact (Finset.sum_le_sum (fun a _ => dyadicIncrementFeature_second_le C θ hθ j x hx _)).trans_eq
    (by simp [mul_assoc])

/-- The finite-coordinate current Gram and the two true vector moment families. -/
def dyadicFinPilotGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ (dyadicPreconditionedGram θ j x)

def dyadicFinPilotMoments {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun response i => preconditionedPilotPopulation θ j x
    (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
      else Sum.inr (Sum.inl (anchoredFinIndex i)))

def dyadicIncrementPopulation {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    incrementVariables (anchoredDimension d ℓ) → ℝ :=
  incrementValuation (dyadicFinPilotGram θ j x)
    (if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)
    (dyadicFinPilotMoments θ j x)
    (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)

/-- Original observation-law integration produces precisely the free-moment
population point, including the deterministic identity/zero root parent. -/
theorem dyadicIncrementFeature_integral {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (v : incrementVariables (anchoredDimension d ℓ)) :
    (∫ z, dyadicIncrementFeature j x v z ∂observationLaw θ) =
      dyadicIncrementPopulation θ j x v := by
  let := observationLaw_isProbability C θ hθ
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
        RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
        anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex,
        preconditionedPilotPopulation] using
        preconditionedPilotPopulation_gram C θ hθ j x hx (anchoredFinIndex i) (anchoredFinIndex t)
    | inr v =>
      by_cases hj : j = 0
      · simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
          RoughRegime.CombinedPolynomial.entryValuation, hj, Matrix.one_apply]
      · simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
          RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
          anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex, hj,
          preconditionedPilotPopulation] using
          preconditionedPilotPopulation_gram C θ hθ (j - 1) x hx
            (anchoredFinIndex v.2.1) (anchoredFinIndex v.2.2)
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent <;> cases response <;> by_cases hj : j = 0
    all_goals simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
      dyadicFinPilotMoments, hj, preconditionedPilotPopulation]

theorem dyadicIncrementRawMean_eq_population {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      dyadicIncrementPopulation θ j x
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  funext a
  exact dyadicIncrementFeature_integral C θ hθ j x hx _

theorem dyadicFinPilotGram_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicFinPilotGram (ℓ := ℓ) θ j x =
      anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  unfold dyadicFinPilotGram dyadicPreconditionedGram anchoredFinNormalizedGram
  rw [dyadicKnownGram_eq_normalized, dyadicPopulationGram_eq_normalized C θ hθ]

theorem dyadicFinPilotMoments_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (t : Bool) (i : Fin (anchoredDimension d ℓ)) :
    dyadicFinPilotMoments θ j x t i =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (if t then fun _ => 1 else θ.regression ∘ dyadicCellAffine j x) (anchoredFinIndex i) := by
  cases t
  · exact preconditionedPilotPopulation_response C θ hθ j x hx _
  · exact preconditionedPilotPopulation_constant C θ hθ j x hx _

theorem dyadicIncrementRawVector_sample_facts {d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    iIndepFun (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector (ℓ := ℓ) j x (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i))) ∧
    (∀ i t : Fin n, IdentDistrib
      (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i))
      (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a ∂sampleLaw θ n) =
      dyadicIncrementRawMean θ j x a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := dyadicIncrementRawVector_measurable (ℓ := ℓ) j x
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
    exact (dyadicIncrementFeature_memLp_two C θ hθ j x hx _).comp_measurePreserving (hp i)
  · intro i a
    exact integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i)
      ((dyadicIncrementFeature_measurable j x
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a)).aestronglyMeasurable)

theorem dyadicIncrementRawVector_sample_second_le {d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (i : Fin n) :
    (∫ z : Fin n → Observation d, ‖dyadicIncrementRawVector (ℓ := ℓ) j x (z i)‖ ^ 2 ∂sampleLaw θ n) ≤
      Fintype.card (incrementVariables (anchoredDimension d ℓ)) *
        preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  unfold sampleLaw
  rw [integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i)
    (((dyadicIncrementRawVector_measurable (ℓ := ℓ) j x).norm.pow_const 2).aestronglyMeasurable)]
  exact dyadicIncrementRawVector_second_le C θ hθ j x hx

end NearlyMinimax
