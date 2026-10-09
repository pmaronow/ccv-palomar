module

public import NearlyMinimax.PoissonCellMoments
public import NearlyMinimax.PoissonCellPairEvents


@[expose] public section

/-! Higher moment bounds for the genuine Poisson cell field, derived from
the fair-sign occupancy formula and two actual disjoint same-cell pairs. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-- Ordered four distinct observation indices, giving two disjoint pairs. -/
abbrev CellMomentQuadruple (j : ℕ) := {q : Fin 4 → Fin j // Function.Injective q}

theorem cellMomentQuadruple_card_le (j : ℕ) :
    Fintype.card (CellMomentQuadruple j) ≤ j^4 := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_subtype_le (fun q : Fin 4 → Fin j => Function.Injective q)

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

def partitionFiberEvenIndicator (ρ : H → X → Fin 2) (n j : ℕ)
    (U : Fin j → X) (h : Fin n → H) : ℝ :=
  if ∀ p : Fin n → Fin 2,
    Even ((Finset.univ.filter (fun l => partitionFieldPattern ρ h (U l) = p)).card)
    then 1 else 0

theorem partitionFiberEvenIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (n j : ℕ) (U : Fin j → X) :
    Measurable (partitionFiberEvenIndicator ρ n j U) := by
  let F : (Fin j → (Fin n → Fin 2)) → ℝ := fun p =>
    if ∀ c : Fin n → Fin 2, Even ((Finset.univ.filter (fun l => p l = c)).card)
      then 1 else 0
  have hF : Measurable F := measurable_of_finite _
  have hp : Measurable (fun h : Fin n → H => fun l => partitionFieldPattern ρ h (U l)) := by
    apply Measurable.of_eval
    intro l
    exact (partitionFieldPattern_measurable ρ hρ n).comp
      (measurable_id.prodMk measurable_const)
  exact hF.comp hp

theorem partitionFiberEvenIndicator_le_pairs (ρ : H → X → Fin 2) (n j : ℕ)
    (hj : 4 ≤ j) (U : Fin j → X) (h : Fin n → H) :
    partitionFiberEvenIndicator ρ n j U h ≤
      ∑ q : CellMomentQuadruple j, partitionFiberBothIndicator ρ n
        (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3)) h := by
  unfold partitionFiberEvenIndicator
  split_ifs with heven
  · obtain ⟨a, _, b, _, c, _, e, _, hba, hca, hcb, hea, heb, hec, hab, hce⟩ :=
      even_cells_two_disjoint_pairs (Finset.univ : Finset (Fin j))
        (fun l => partitionFieldPattern ρ h (U l)) (by simpa using hj) heven
    have hinj : Function.Injective (![a,b,c,e] : Fin 4 → Fin j) := by
      intro i l hil
      fin_cases i <;> fin_cases l <;> simp_all
    let q : CellMomentQuadruple j := ⟨![a,b,c,e], hinj⟩
    have hq : partitionFiberBothIndicator ρ n
        (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3)) h = 1 := by
      simp only [q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, partitionFiberBothIndicator]
      simp [hab.symm, hce.symm]
    rw [← hq]
    exact Finset.single_le_sum (f := fun q : CellMomentQuadruple j =>
      partitionFiberBothIndicator ρ n (U (q.val 0)) (U (q.val 1))
        (U (q.val 2)) (U (q.val 3)) h) (fun q _ => by
      unfold partitionFiberBothIndicator
      split_ifs <;> norm_num) (Finset.mem_univ q)
  · apply Finset.sum_nonneg
    intro q _
    unfold partitionFiberBothIndicator
    split_ifs <;> norm_num

def poissonCellEvenIndicator (ρ : H → X → Fin 2) (j : ℕ) (U : Fin j → X)
    (z : partitionFieldMark H) : ℝ := partitionFiberEvenIndicator ρ z.1 j U z.2.1

theorem poissonCellEvenIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (j : ℕ) (U : Fin j → X) :
    Measurable (poissonCellEvenIndicator ρ j U) :=
  measurable_sigma_of_fibers _ (fun n =>
    (partitionFiberEvenIndicator_measurable ρ hρ n j U).comp measurable_fst)

/-- The actual field moment is the probability of even occupancy, from the
constructed independent fair signs and the true Poisson mark law. -/
theorem poissonCellField_product_moment_eq_even (μ : Measure H) [IsProbabilityMeasure μ]
    (r : ℝ≥0) (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ))
    (j : ℕ) (U : Fin j → X) :
    (∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r) =
      ∫ z, poissonCellEvenIndicator ρ j U z ∂poissonCellFieldLaw μ r := by
  rw [poissonCellField_integral_series μ r _
    (Finset.measurable_prod _ (fun l _ => poissonCellFieldValue_measurable_fixed ρ hρ (U l)))
    (fun z => by simp only [Finset.abs_prod, poissonCellFieldValue_abs,
      Finset.prod_const_one, le_refl]),
    poissonCellField_integral_series μ r _ (poissonCellEvenIndicator_measurable ρ hρ j U)
      (fun z => by unfold poissonCellEvenIndicator partitionFiberEvenIndicator
                   split_ifs <;> norm_num)]
  apply tsum_congr
  intro n
  congr 1
  change (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) = _
  rw [partitionFieldFiber_product_moment μ ρ hρ n j U]
  change (∫ h, partitionFiberEvenIndicator ρ n j U h ∂Measure.pi (fun _ : Fin n => μ)) =
    ∫ z, partitionFiberEvenIndicator ρ n j U z.1
      ∂(Measure.pi (fun _ : Fin n => μ)).prod (cellSignLaw (Fin n → Fin 2))
  rw [integral_fun_fst]
  simp

/-- The higher field moment is bounded by the genuine probabilities of two
disjoint same-cell pairs, with no assumed field moment bound. -/
theorem poissonCellField_product_moment_le_two_pair_probabilities
    (μ : Measure H) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ))
    (j : ℕ) (hj : 4 ≤ j) (U : Fin j → X) :
    (∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r) ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-(r : ℝ) *
        (1 - partitionBothProbability μ ρ (U (q.val 0)) (U (q.val 1))
          (U (q.val 2)) (U (q.val 3)))) := by
  rw [poissonCellField_product_moment_eq_even μ r ρ hρ j U]
  have hi : Integrable (poissonCellEvenIndicator ρ j U) (poissonCellFieldLaw μ r) :=
    Integrable.of_bound (poissonCellEvenIndicator_measurable ρ hρ j U).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        unfold poissonCellEvenIndicator partitionFiberEvenIndicator
        split_ifs <;> norm_num))
  have hq (q : CellMomentQuadruple j) : Integrable (poissonCellBothIndicator ρ
      (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3))) (poissonCellFieldLaw μ r) :=
    Integrable.of_bound (poissonCellBothIndicator_measurable ρ hρ _ _ _ _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        unfold poissonCellBothIndicator partitionFiberBothIndicator
        split_ifs <;> norm_num))
  calc
    _ ≤ ∫ z, ∑ q : CellMomentQuadruple j, poissonCellBothIndicator ρ
        (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3)) z ∂poissonCellFieldLaw μ r :=
      integral_mono hi (integrable_finsetSum Finset.univ (fun q _ => hq q))
        (fun z => partitionFiberEvenIndicator_le_pairs ρ z.1 j hj U z.2.1)
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun q _ => hq q)]
      apply Finset.sum_congr rfl
      intro q _
      exact poissonCellBothIndicator_integral μ r ρ hρ _ _ _ _

/-- The union separation probability dominates half the sum of the two
individual separation probabilities. This comes from the actual indicators. -/
theorem partition_union_separation_ge_half (μ : Measure H) [IsProbabilityMeasure μ]
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (a b c e : X) :
    ((1 - partitionSameProbability μ ρ a b) +
      (1 - partitionSameProbability μ ρ c e)) / 2 ≤
        1 - partitionBothProbability μ ρ a b c e := by
  have hp : Integrable (fun h => pairSameIndicator ρ a b h * pairSameIndicator ρ c e h) μ :=
    Integrable.of_bound
      ((pairSameIndicator_measurable ρ hρ a b).mul
        (pairSameIndicator_measurable ρ hρ c e)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun h => by
        unfold pairSameIndicator
        split_ifs <;> norm_num))
  have hs := ((pairSameIndicator_integrable μ ρ hρ a b).add
    (pairSameIndicator_integrable μ ρ hρ c e)).div_const 2
  have h := integral_mono hp hs (fun h => show
      pairSameIndicator ρ a b h * pairSameIndicator ρ c e h ≤
        (pairSameIndicator ρ a b h + pairSameIndicator ρ c e h) / 2 by
      unfold pairSameIndicator
      split_ifs <;> norm_num)
  rw [integral_div] at h
  change (∫ h, pairSameIndicator ρ a b h * pairSameIndicator ρ c e h ∂μ) ≤
    (∫ h, pairSameIndicator ρ a b h + pairSameIndicator ρ c e h ∂μ) / 2 at h
  rw [integral_add (pairSameIndicator_integrable μ ρ hρ a b)
    (pairSameIndicator_integrable μ ρ hρ c e)] at h
  change partitionBothProbability μ ρ a b c e ≤
    (partitionSameProbability μ ρ a b + partitionSameProbability μ ρ c e) / 2 at h
  linarith

/-- The source two-pair exponential higher-moment envelope for the actual
constructed Poisson cell field, for all orders at least four. -/
theorem poissonCellField_product_moment_abs_le_two_pairs
    (μ : Measure H) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ))
    (j : ℕ) (hj : 4 ≤ j) (U : Fin j → X) :
    |∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-(r : ℝ) / 2 *
        ((1 - partitionSameProbability μ ρ (U (q.val 0)) (U (q.val 1))) +
          (1 - partitionSameProbability μ ρ (U (q.val 2)) (U (q.val 3))))) := by
  rw [abs_of_nonneg (poissonCellField_product_moment_nonneg μ r ρ hρ j U)]
  apply (poissonCellField_product_moment_le_two_pair_probabilities μ r ρ hρ j hj U).trans
  apply Finset.sum_le_sum
  intro q _
  apply Real.exp_le_exp.mpr
  have h := partition_union_separation_ge_half μ ρ hρ
    (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3))
  nlinarith only [h, r.coe_nonneg]

end NearlyMinimax
