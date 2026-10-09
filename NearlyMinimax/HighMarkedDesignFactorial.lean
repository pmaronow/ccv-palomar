module

public import NearlyMinimax.HighMarkedResponseEnergy
public import NearlyMinimax.SpatialSubsetEnergy


@[expose] public section

/-! The complete marked generator under its actual iid normalized design.
The factorial series contains genuine raw numerator integrals over the
selected patch observations; no local or global target budget is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem iid_cell_selected_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α)
    (S : Finset (Fin n)) (H : (S → α) → ℝ)
    (hH : Integrable H (Measure.pi (fun _ : S => μ.restrict A))) :
    IntegrableOn (fun x : Fin n → α => H (fun i : S => x i.val))
      (designMembershipCell n A S) (Measure.pi (fun _ : Fin n => μ)) := by
  rw [IntegrableOn, designMembershipCell, Measure.restrict_pi_pi]
  have hs := measurePreserving_piEquivPiSubtypeProd
    (fun i : Fin n => μ.restrict (if i ∈ S then A else Aᶜ)) (fun i => i ∈ S)
  have hι : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
  rw [hι] at hs
  have hin : (fun i : S => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
      (fun _ : S => μ.restrict A) := by
    funext i
    rw [ite_eq_left i.property]
  have hout : (fun i : {i : Fin n // i ∉ S} => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
      (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ) := by
    funext i
    rw [ite_eq_right i.property]
  rw [hin, hout] at hs
  have hp : Integrable (fun z : (S → α) × ({i : Fin n // i ∉ S} → α) => H z.1)
      ((Measure.pi (fun _ : S => μ.restrict A)).prod
        (Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ))) := hH.comp_fst _
  have hh := hs.integrable_comp_of_integrable hp
  exact hh

theorem iid_energy_integrable_of_selected {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (E : (Fin n → α) → ℝ) (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (he : ∀ S x, x ∈ designMembershipCell n A S → E x = H S (fun i : S => x i.val)) :
    Integrable E (Measure.pi (fun _ : Fin n => μ)) := by
  have hcover : (⋃ S : Finset (Fin n), designMembershipCell n A S) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
    rw [design_membership_cell_iff]
    intro i
    simp
  have hi : IntegrableOn E (⋃ S : Finset (Fin n), designMembershipCell n A S)
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply integrableOn_finite_iUnion.mpr
    intro S
    have hsel := iid_cell_selected_integrable μ n A S (H S) (hH S)
    apply hsel.congr
    filter_upwards [ae_restrict_mem (design_membership_cell_measurable n A hA S)] with x hx
    exact (he S x hx).symm
  simpa only [hcover, integrableOn_univ] using hi

section
variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

def highMarkedResponseMass (a V η : ℝ) (g w : α → ℝ) (φ : α → ι → ℝ)
    (c : ι → ℝ) (x : α) (y : Fin 3) : ℝ :=
  ternaryMass a (g x + η * w x * ∑ γ, φ x γ * c γ) V y

def highMarkedSampleNumerator (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ)
    (x : Fin r → α) (y : Fin r → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η (fun z => pReset z ∘ x) cReset
    (g ∘ x) (w ∘ x) (φ ∘ x) y - η ^ 2 * (∏ i, p (x i)) *
      ∑ i, (w (x i)) ^ 2 * highResponseVarianceTerm a V η (g ∘ x) (w ∘ x) (φ ∘ x) c y i

def highMarkedSampleConditionalEnergy (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α) : ℝ :=
  selectedConditionalScoreEnergy p (highMarkedResponseMass a V η g w φ c)
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x

theorem high_marked_sample_score_eq_ratio (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α) (y : Fin r → Fin 3) :
    highMarkedLocalScore π activation a V η (p ∘ x) (fun z => pReset z ∘ x) cReset
      (g ∘ x) (w ∘ x) (φ ∘ x) c y =
    highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y /
      selectedRawLikelihood p (highMarkedResponseMass a V η g w φ c) x y := rfl

theorem high_marked_sample_energy_integral (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (ha : a ≠ 0) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α)
    (hp : ∀ z y, 0 < highMarkedResponseMass a V η g w φ c z y) :
    (∫ y, highMarkedLocalScore π activation a V η (p ∘ x) (fun z => pReset z ∘ x) cReset
      (g ∘ x) (w ∘ x) (φ ∘ x) c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a
        (coefficientRegression η (g ∘ x) (w ∘ x) (φ ∘ x) c i) V ha (fun y => (hp (x i) y).le))) =
    highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c x := by
  rw [ternary_index_product_integral]
  unfold highMarkedSampleConditionalEnergy selectedConditionalScoreEnergy
  simp_rw [← high_marked_sample_score_eq_ratio r π activation a V η p pReset cReset g w φ c x]
  apply Finset.sum_congr (by ext y; simp)
  intro y hy
  rfl

def selectedDesignEnumeration {n : ℕ} (S : Finset (Fin n)) : Fin S.card ≃ S :=
  (S.orderIsoOfFin rfl).toEquiv

def selectedDesignEmbedding {n : ℕ} (S : Finset (Fin n)) : Fin S.card ↪ Fin n :=
  (S.orderEmbOfFin rfl).toEmbedding

theorem selected_design_embedding_map {n : ℕ} (S : Finset (Fin n)) :
    Finset.univ.map (selectedDesignEmbedding S) = S := Finset.map_orderEmbOfFin_univ S rfl

theorem high_marked_sample_energy_cell_selected {n : ℕ} (A : Set α)
    (S : Finset (Fin n)) (x : Fin n → α) (hx : x ∈ designMembershipCell n A S)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ z, p z ≠ 0) (hp : ∀ z y, 0 < highMarkedResponseMass a V η g w φ c z y)
    (hw : ∀ z, z ∉ A → w z = 0) (hReset : ∀ e z, z ∉ A → pReset e z = p z) :
    highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x =
      highMarkedSampleConditionalEnergy S.card π activation a V η p pReset cReset g w φ c
        (x ∘ selectedDesignEmbedding S) := by
  have hmem := design_membership_cell_iff n A S x |>.mp hx
  have hwo (i : Fin n) (hi : i ∉ Finset.univ.map (selectedDesignEmbedding S)) : w (x i) = 0 := by
    rw [selected_design_embedding_map] at hi
    exact hw _ (fun h => hi ((hmem i).mp h))
  have hro (e : E) (i : Fin n) (hi : i ∉ Finset.univ.map (selectedDesignEmbedding S)) :
      pReset e (x i) = p (x i) := by
    rw [selected_design_embedding_map] at hi
    exact hReset e _ (fun h => hi ((hmem i).mp h))
  have he := high_marked_selected_response_energy (selectedDesignEmbedding S) π activation a V η ha
    (p ∘ x) (fun z => pReset z ∘ x) cReset (g ∘ x) (w ∘ x) (φ ∘ x) c
    (fun i => hpd (x i)) (fun i y => hp (x i) y) hwo hro
  rw [high_marked_sample_energy_integral n π activation a V η ha p pReset cReset g w φ c x hp] at he
  have hs := high_marked_sample_energy_integral S.card π activation a V η ha p pReset cReset
    g w φ c (x ∘ selectedDesignEmbedding S) hp
  change _ = (∫ y, highMarkedLocalScore π activation a V η (p ∘ (x ∘ selectedDesignEmbedding S))
    (fun z => pReset z ∘ (x ∘ selectedDesignEmbedding S)) cReset
    (g ∘ (x ∘ selectedDesignEmbedding S)) (w ∘ (x ∘ selectedDesignEmbedding S))
    (φ ∘ (x ∘ selectedDesignEmbedding S)) c y ^ 2 ∂_) at he
  exact he.trans hs

theorem high_marked_design_raw_factorial_series (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) (A : Set α) (hA : MeasurableSet A) (m pMinus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : α → ℝ) (hpMeas : Measurable p) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ)
    (hqMeas : ∀ y, Measurable (fun x => highMarkedResponseMass a V η g w φ c x y))
    (hprob : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hpd : ∀ x, pMinus ≤ p x)
    (hp : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hw : ∀ x, x ∉ A → w x = 0) (hReset : ∀ e x, x ∉ A → pReset e x = p x)
    (hRMeas : ∀ r y, Measurable (fun x => highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y))
    (hRaw : ∀ r, Integrable (selectedRawSquareEnergy
      (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c))
        (Measure.pi (fun _ : Fin r => ν.restrict A))) :
    Integrable (highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c)
      (Measure.pi (fun _ : Fin n => ν.withDensity (fun x => ENNReal.ofReal (p x / m)))) ∧
    (∫ x, highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x
      ∂Measure.pi (fun _ : Fin n => ν.withDensity (fun x => ENNReal.ofReal (p x / m)))) ≤
      ∑ r ∈ Finset.range (n + 1),
        ((n : ℝ) * highFixedScoreDenominator pMinus cMass) ^ r / (r.factorial : ℝ) *
          ∫ x, selectedRawSquareEnergy
            (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
              ∂Measure.pi (fun _ : Fin r => ν.restrict A) := by
  let μ := ν.withDensity (fun x => ENNReal.ofReal (p x / m))
  let _ : IsProbabilityMeasure μ := hprob
  let F (r : ℕ) := highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c
  let H (S : Finset (Fin n)) (z : S → α) : ℝ := F S.card (z ∘ selectedDesignEnumeration S)
  let J (r : ℕ) := ∫ x, selectedRawSquareEnergy
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
      ∂Measure.pi (fun _ : Fin r => ν.restrict A)
  have hp0 (x : α) : p x ≠ 0 := (hpMinus.trans_le (hpd x)).ne'
  have hq0 (x : α) (y : Fin 3) : 0 < highMarkedResponseMass a V η g w φ c x y := hcMass.trans_le (hp x y)
  have hFI (r : ℕ) := normalized_selected_score_energy_integrable_bound ν A hA m pMinus cMass
    hpMinus hcMass hm p hpMeas (highMarkedResponseMass a V η g w φ c) hqMeas
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) (hRMeas r) hprob
    (fun x _ => hpd x) (fun x _ y => hp x y) (hRaw r)
  have hHI (S : Finset (Fin n)) : Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)) :=
    finite_pi_reindex_integrable (μ.restrict A) (selectedDesignEnumeration S).symm (F S.card) (hFI S.card).1
  have hEq (S : Finset (Fin n)) (x : Fin n → α) (hx : x ∈ designMembershipCell n A S) :
      F n x = H S (fun i : S => x i.val) :=
    high_marked_sample_energy_cell_selected A S x hx π activation a V η ha p pReset cReset
      g w φ c hp0 hq0 hw hReset
  have hFn : Integrable (F n) (Measure.pi (fun _ : Fin n => μ)) :=
    iid_energy_integrable_of_selected μ n A hA (F n) H hHI hEq
  refine ⟨hFn, ?_⟩
  apply iid_local_energy_le_factorial_spatial_series μ n A hA (F n) hFn H hHI
    (fun S z => selected_conditional_score_energy_nonneg p (highMarkedResponseMass a V η g w φ c)
      (fun x y => (hq0 x y).le) _ _) (fun S x hx => (hEq S x hx).le)
    (highFixedScoreDenominator pMinus cMass) (high_fixed_score_denominator_pos hpMinus hcMass).le J
    (fun r => integral_nonneg (fun x => Finset.sum_nonneg (fun y _ => sq_nonneg _)))
  intro S
  change (∫ z, F S.card (z ∘ selectedDesignEnumeration S) ∂Measure.pi (fun _ : S => μ.restrict A)) ≤ _
  have he : (∫ z, F S.card (z ∘ selectedDesignEnumeration S) ∂Measure.pi (fun _ : S => μ.restrict A)) =
      ∫ z, F S.card z ∂Measure.pi (fun _ : Fin S.card => μ.restrict A) :=
    finite_pi_reindex_integral (μ.restrict A) (selectedDesignEnumeration S).symm (F S.card)
  rw [he]
  have hs := (hFI S.card).2
  simp only [Fintype.card_fin] at hs
  change (∫ z, F S.card z ∂Measure.pi (fun _ : Fin S.card => μ.restrict A)) ≤
    highFixedScoreDenominator pMinus cMass ^ S.card * J S.card at hs
  exact hs

end
end NearlyMinimax
