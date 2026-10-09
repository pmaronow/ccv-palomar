module

public import NearlyMinimax.LowSmoothnessVariance


@[expose] public section

/-! # IID design patch counts

Patch membership is measured under an actual product probability measure
on the design sample. The binomial law is derived by partitioning that
sample space into disjoint membership cells.
-/

namespace NearlyMinimax

open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Number of iid design observations falling in a patch. -/
def designPatchCount {α : Type*} (n : ℕ) (A : Set α) (x : Fin n → α) : ℕ :=
  (Finset.univ.filter fun i => x i ∈ A).card

/-- The cell with precisely the observation indices in `s` inside the patch. -/
def designMembershipCell {α : Type*} (n : ℕ) (A : Set α) (s : Finset (Fin n)) : Set (Fin n → α) :=
  Set.pi Set.univ (fun i => if i ∈ s then A else Aᶜ)

theorem design_patch_count_le {α : Type*} (n : ℕ) (A : Set α) (x : Fin n → α) :
    designPatchCount n A x ≤ n := by
  unfold designPatchCount
  simpa using Finset.card_le_card (Finset.filter_subset (fun i => x i ∈ A) Finset.univ)

theorem design_membership_cell_iff {α : Type*} (n : ℕ) (A : Set α)
    (s : Finset (Fin n)) (x : Fin n → α) :
    x ∈ designMembershipCell n A s ↔ ∀ i, x i ∈ A ↔ i ∈ s := by
  simp only [designMembershipCell, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h i
    by_cases hi : i ∈ s
    · simpa [hi] using h i
    · simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ s
    · simpa [hi] using (h i).mpr hi
    · simpa [hi] using (h i).not.mpr hi

theorem design_membership_cell_measurable {α : Type*} [MeasurableSpace α]
    (n : ℕ) (A : Set α) (hA : MeasurableSet A) (s : Finset (Fin n)) :
    MeasurableSet (designMembershipCell n A s) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i _
  split_ifs
  · exact hA
  · exact hA.compl

theorem design_membership_cells_disjoint {α : Type*} (n : ℕ) (A : Set α) :
    Pairwise (fun s t : Finset (Fin n) => Disjoint (designMembershipCell n A s) (designMembershipCell n A t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  apply hst
  ext i
  exact ((design_membership_cell_iff n A s x).mp hs i).symm.trans
    ((design_membership_cell_iff n A t x).mp ht i)

/-- The count event is a disjoint union of cells indexed by subsets of its count. -/
theorem design_patch_count_fiber {α : Type*} (n : ℕ) (A : Set α) (k : ℕ) :
    {x : Fin n → α | designPatchCount n A x = k} =
      ⋃ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, designMembershipCell n A s := by
  ext x
  constructor
  · intro hx
    change designPatchCount n A x = k at hx
    let s : Finset (Fin n) := Finset.univ.filter fun i => x i ∈ A
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, hx⟩
    · rw [design_membership_cell_iff]
      intro i
      simp [s]
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hfilter : (Finset.univ.filter fun i => x i ∈ A) = s := by
      ext i
      simpa using (design_membership_cell_iff n A s x).mp hxs i
    change (Finset.univ.filter fun i => x i ∈ A).card = k
    rw [hfilter]
    exact (Finset.mem_powersetCard.mp hs).2

/-- Membership cells have the product Bernoulli probabilities dictated by
independence under the iid design product measure. -/
theorem iid_design_membership_cell_measure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α)
    (s : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => μ)) (designMembershipCell n A s) =
      (μ A) ^ s.card * (μ Aᶜ) ^ (n - s.card) := by
  rw [designMembershipCell, Measure.pi_pi]
  simp only [apply_ite]
  rw [Finset.prod_ite]
  have hin : (Finset.univ.filter fun i : Fin n => i ∈ s) = s := by ext i; simp
  have hout : (Finset.univ.filter fun i : Fin n => i ∉ s) = Finset.univ \ s := by ext i; simp
  rw [hin, hout]
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ s)]

/-- Exact binomial count law, in real probabilities, for an arbitrary measurable
patch under an arbitrary iid design probability measure. -/
theorem iid_design_patch_count_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A) (k : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)).real {x : Fin n → α | designPatchCount n A x = k} =
      binomialCountMass n (μ.real A) k := by
  rw [measureReal_def, design_patch_count_fiber]
  rw [measure_biUnion_finset]
  · rw [ENNReal.toReal_sum (fun s _ => measure_ne_top _ _)]
    have hcell (s : Finset (Fin n)) (hs : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
        ((Measure.pi (fun _ : Fin n => μ)) (designMembershipCell n A s)).toReal =
          (μ.real A) ^ k * (1 - μ.real A) ^ (n - k) := by
      rw [iid_design_membership_cell_measure, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
      rw [(Finset.mem_powersetCard.mp hs).2]
      have hcompl : μ.real Aᶜ = 1 - μ.real A := by
        simpa using measureReal_compl hA (μ := μ)
      change (μ.real A) ^ k * (μ.real Aᶜ) ^ (n - k) = _
      rw [hcompl]
    rw [Finset.sum_congr rfl hcell]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
    unfold binomialCountMass
    ring
  · intro s hs t ht hst
    exact design_membership_cells_disjoint n A hst
  · intro s _
    exact design_membership_cell_measurable n A hA s

/-- The patch count is a measurable random variable. -/
theorem design_patch_count_measurable {α : Type*} [MeasurableSpace α]
    (n : ℕ) (A : Set α) (hA : MeasurableSet A) : Measurable (designPatchCount n A) := by
  have heq : designPatchCount n A =
      (fun x : Fin n → α => ∑ i : Fin n, if x i ∈ A then (1 : ℕ) else 0) := by
    funext x
    exact Finset.card_filter _ _
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hA.preimage (measurable_pi_apply i)) measurable_const measurable_const

/-- Every finite function of the actual patch count integrates against its
binomial law. This connects the counting estimate to the iid design measure. -/
theorem iid_design_count_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (e : ℕ → ℝ) :
    (∫ x : Fin n → α, e (designPatchCount n A x) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ k ∈ Finset.range (n + 1), binomialCountMass n (μ.real A) k * e k := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  have hm (k : ℕ) : MeasurableSet {x : Fin n → α | designPatchCount n A x = k} :=
    (measurableSet_singleton k).preimage (design_patch_count_measurable n A hA)
  have hdecomp (x : Fin n → α) : e (designPatchCount n A x) =
      ∑ k ∈ Finset.range (n + 1),
        ({x : Fin n → α | designPatchCount n A x = k}).indicator (fun _ => e k) x := by
    symm
    calc
      _ = ({x : Fin n → α | designPatchCount n A x = designPatchCount n A x}).indicator
          (fun _ => e (designPatchCount n A x)) x := by
        apply Finset.sum_eq_single (designPatchCount n A x)
        · intro k _ hk
          simp [Ne.symm hk]
        · intro hn
          exact False.elim (hn (Finset.mem_range.mpr
            (Nat.lt_succ_iff.mpr (design_patch_count_le n A x))))
      _ = e (designPatchCount n A x) := by simp
  have hfun : (fun x : Fin n → α => e (designPatchCount n A x)) =
      (fun x => ∑ k ∈ Finset.range (n + 1),
        ({x : Fin n → α | designPatchCount n A x = k}).indicator (fun _ => e k) x) := funext hdecomp
  rw [hfun, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_indicator_const (e k) (hm k), iid_design_patch_count_probability μ n A hA k]
    simp [smul_eq_mul]
  · intro k _
    exact (integrable_const (e k)).indicator (hm k)

/-- Integration of a genuine iid patch count gives the quadratic collision
energy bound, without assuming a binomial count law as a hypothesis. -/
theorem iid_design_collision_energy_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (C η : ℝ) (e : ℕ → ℝ) (hC : 0 ≤ C) (hmean : n * μ.real A ≤ 1)
    (he0 : e 0 = 0) (he1 : e 1 = 0) (he : ∀ k, 2 ≤ k → e k ≤ C ^ k * η ^ 4) :
    (∫ x : Fin n → α, e (designPatchCount n A x) ∂Measure.pi (fun _ : Fin n => μ)) ≤
      C ^ 2 * Real.exp C * η ^ 4 * (n * μ.real A) ^ 2 := by
  rw [iid_design_count_integral μ n A hA e]
  exact binomial_collision_energy_bound n (μ.real A) C η e measureReal_nonneg
    measureReal_le_one hC hmean he0 he1 he

/-- The response-score energy bound transfers to an actual iid design patch
count under any probability measure and any measurable patch. -/
theorem iid_design_patch_score_energy_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (a V η z ρ c : ℝ) (g w : (k : ℕ) → Fin k → ℝ)
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c) (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : n * μ.real A ≤ 1)
    (hw : ∀ k, 2 ≤ k → ∀ i, |w k i| ≤ 1)
    (hreg : ∀ k, 2 ≤ k → ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i,
      |g k i + η * w k i * u| ≤ ρ)
    (hq : ∀ k, 2 ≤ k → ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ i y,
      0 ≤ ternaryMass a (g k i + η * w k i * u) V y ∧
        ternaryMass a (g k i + η * w k i * u) V y ≤ 1)
    (hlower : ∀ k, 2 ≤ k → ∀ i y, c ≤ ternaryMass a (g k i + η * w k i * z) V y) :
    (∫ x : Fin n → α,
      patchExpectedScoreEnergy (designPatchCount n A x) a V η
        (g (designPatchCount n A x)) (w (designPatchCount n A x)) z
        ∂Measure.pi (fun _ : Fin n => μ)) ≤
      (ternaryScoreExponentialConstant a ρ c) ^ 2 *
        Real.exp (ternaryScoreExponentialConstant a ρ c) * η ^ 4 * (n * μ.real A) ^ 2 := by
  rw [iid_design_count_integral μ n A hA
    (fun k => patchExpectedScoreEnergy k a V η (g k) (w k) z)]
  exact binomial_patch_score_energy_bound n a V η z ρ c (μ.real A) g w ha hρ hc hz
    measureReal_nonneg measureReal_le_one hmean hw hreg hq hlower

end

end NearlyMinimax
