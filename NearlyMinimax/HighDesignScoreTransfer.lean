module

public import NearlyMinimax.DesignCounts
public import NearlyMinimax.HighObservationLaw
public import NearlyMinimax.HighUnionFieldScore


@[expose] public section

/-! Actual iid membership-cell and normalized-design transfers. The
independent count law and unused-observation factors are derived from the
actual product probability experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- Exact selected-coordinate integral on an actual membership cell.
No independence or binomial-weight premise is supplied. -/
theorem iid_selected_membership_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α)
    (S : Finset (Fin n)) (H : (S → α) → ℝ) :
    (∫ x in designMembershipCell n A S, H (fun i : S => x i.val)
      ∂Measure.pi (fun _ : Fin n => μ)) =
      (μ.real Aᶜ) ^ (n - S.card) *
        ∫ z, H z ∂Measure.pi (fun _ : S => μ.restrict A) := by
  let μi : Fin n → Measure α := fun i => μ.restrict (if i ∈ S then A else Aᶜ)
  have hm : (Measure.pi (fun _ : Fin n => μ)).restrict (designMembershipCell n A S) = Measure.pi μi :=
    Measure.restrict_pi_pi (fun _ : Fin n => μ) (fun i => if i ∈ S then A else Aᶜ)
  have hs := measurePreserving_piEquivPiSubtypeProd μi (fun i : Fin n => i ∈ S)
  have hι : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
  rw [hι] at hs
  have he := hs.integral_comp' (fun z => H z.1)
  change (∫ x, H (fun i : S => x i.val) ∂Measure.pi μi) = _ at he
  rw [hm, he]
  have hin : (fun i : S => μi i.val) = (fun _ : S => μ.restrict A) := by
    funext i
    simp only [μi, ite_eq_left i.property]
  have hout : (fun i : {i : Fin n // i ∉ S} => μi i.val) =
      (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ) := by
    funext i
    simp only [μi, ite_eq_right i.property]
  rw [hin, hout]
  have hint := integral_prod_mul (μ := Measure.pi (fun _ : S => μ.restrict A))
    (ν := Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ)) H (fun _ => (1 : ℝ))
  simp only [mul_one] at hint
  have hcard : Fintype.card {i : Fin n // i ∉ S} = n - S.card := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ = (∫ z, H z ∂Measure.pi (fun _ : S => μ.restrict A)) *
      (∫ z : {i : Fin n // i ∉ S} → α, (1 : ℝ) ∂Measure.pi (fun _ => μ.restrict Aᶜ)) := hint
    _ = _ := by
      rw [integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, Measure.pi_univ, Measure.restrict_apply_univ,
        Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, hcard]
      ring

/-- Every measurable iid patch admits the true disjoint membership-cell
partition of an integrable data function. -/
theorem iid_integral_eq_membership_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (H : (Fin n → α) → ℝ) (hH : Integrable H (Measure.pi (fun _ : Fin n => μ))) :
    (∫ x, H x ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ S : Finset (Fin n), ∫ x in designMembershipCell n A S, H x
        ∂Measure.pi (fun _ : Fin n => μ) := by
  have hcover : (⋃ S : Finset (Fin n), designMembershipCell n A S) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
    rw [design_membership_cell_iff]
    intro i
    simp
  rw [← setIntegral_univ, ← hcover]
  exact integral_iUnion_fintype (fun S => design_membership_cell_measurable n A hA S)
    (design_membership_cells_disjoint n A) (fun S => hH.integrableOn)

/-- Conditional iid energy is bounded by the actual selected-observation
energies; the unused-observation probability is bounded by one. -/
theorem iid_local_energy_le_selected_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (E : (Fin n → α) → ℝ) (hE : Integrable E (Measure.pi (fun _ : Fin n => μ)))
    (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S (fun i : S => x i.val)) :
    (∫ x, E x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ S : Finset (Fin n), ∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A) := by
  rw [iid_integral_eq_membership_sum μ n A hA E hE]
  apply Finset.sum_le_sum
  intro S hS
  have hm : (Measure.pi (fun _ : Fin n => μ)).restrict (designMembershipCell n A S) =
      Measure.pi (fun i => μ.restrict (if i ∈ S then A else Aᶜ)) :=
    Measure.restrict_pi_pi _ _
  have hs := measurePreserving_piEquivPiSubtypeProd
    (fun i : Fin n => μ.restrict (if i ∈ S then A else Aᶜ)) (fun i => i ∈ S)
  have hι : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
  rw [hι] at hs
  have hp : Integrable (fun z : (S → α) × ({i : Fin n // i ∉ S} → α) => H S z.1)
      ((Measure.pi (fun _ : S => μ.restrict A)).prod
        (Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ))) := by
    have hh := (hH S).mul_prod (integrable_const (1 : ℝ)
      (μ := Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ)))
    simpa only [mul_one] using hh
  have hselected : Integrable (fun x : Fin n → α => H S (fun i : S => x i.val))
      ((Measure.pi (fun _ : Fin n => μ)).restrict (designMembershipCell n A S)) := by
    rw [hm]
    have hin : (fun i : S => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
        (fun _ : S => μ.restrict A) := by
      funext i
      rw [ite_eq_left i.property]
    have hout : (fun i : {i : Fin n // i ∉ S} => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
        (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ) := by
      funext i
      rw [ite_eq_right i.property]
    rw [hin, hout] at hs
    have hh := (hs.integrable_comp_emb (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => α)
      (fun i => i ∈ S)).measurableEmbedding).mpr hp
    change Integrable (fun x : Fin n → α => H S (fun i : S => x i.val))
      (Measure.pi (fun i => μ.restrict (if i ∈ S then A else Aᶜ))) at hh
    exact hh

  calc
    _ ≤ ∫ x in designMembershipCell n A S, H S (fun i : S => x i.val) ∂Measure.pi (fun _ : Fin n => μ) := by
      apply integral_mono_ae hE.integrableOn hselected
      filter_upwards [ae_restrict_mem (design_membership_cell_measurable n A hA S)] with x hx
      exact hdom S x hx
    _ = (μ.real Aᶜ) ^ (n - S.card) * ∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A) :=
      iid_selected_membership_integral μ n A S (H S)
    _ ≤ _ := by
      have hmass : (μ.real Aᶜ) ^ (n - S.card) ≤ 1 := pow_le_one₀ measureReal_nonneg measureReal_le_one
      exact (mul_le_mul_of_nonneg_right hmass (integral_nonneg (hHn S))).trans_eq (one_mul _)

end NearlyMinimax
