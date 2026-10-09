module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.FinePairMatrixCost


@[expose] public section

/-! Genuine even-subset expansion of the fine density/response row.
The time-weighted field moments are integrals of the actual hyperplane law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def finePairEvenSelector (j : ℕ) : ℝ := if j = 0 then 0 else if Even j then 1 else 0

theorem finePairEvenSelector_split (j : ℕ) :
    finePairEvenSelector j = (if j = 2 then 1 else 0) +
      (if 4 ≤ j ∧ Even j then 1 else 0) := by
  by_cases hj0 : j = 0
  · simp [finePairEvenSelector, hj0]
  by_cases hj2 : j = 2
  · simp [finePairEvenSelector, hj2]
  by_cases hj : Even j
  · have hj4 : 4 ≤ j := by rcases hj with ⟨l, hl⟩; omega
    simp [finePairEvenSelector, hj0, hj2, hj, hj4]
  · simp [finePairEvenSelector, hj0, hj2, hj]

theorem finePairTimeField_product_measurable {d n : ℕ} (U : Fin n → Covariate d)
    (S : Finset (Fin n)) :
    Measurable (fun e : ℝ × FinePairFieldMark d => ∏ i ∈ S, finePairTimeFieldValue e (U i)) :=
  Finset.measurable_fun_prod S (fun i _ =>
    (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)

theorem finePairTimeField_product_abs {d n : ℕ} (U : Fin n → Covariate d)
    (S : Finset (Fin n)) (e : ℝ × FinePairFieldMark d) :
    |∏ i ∈ S, finePairTimeFieldValue e (U i)| = 1 := by
  rw [Finset.abs_prod]
  simp only [finePairTimeFieldValue_abs, Finset.prod_const_one]

theorem finePairTimeField_weighted_product_integrable {d n : ℕ} [NeZero d]
    (lo hi : ℝ) (U : Fin n → Covariate d) (S : Finset (Fin n)) :
    Integrable (fun e : ℝ × FinePairFieldMark d =>
      e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i))) (finePairTimeFieldMeasure d lo hi) :=
  (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
    (finePairTimeField_product_measurable U S).aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, finePairTimeField_product_abs])

def finePairTimeSubsetMoment {d n : ℕ} (lo hi : ℝ) (U : Fin n → Covariate d)
    (S : Finset (Fin n)) : ℝ :=
  ∫ e : ℝ × FinePairFieldMark d,
    e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i)) ∂finePairTimeFieldMeasure d lo hi

theorem finePairTimeSubsetMoment_actual {d n : ℕ} [NeZero d]
    (lo hi : ℝ) (U : Fin n → Covariate d) (S : Finset (Fin n)) :
    finePairTimeSubsetMoment lo hi U S =
      ∫ T in Icc lo hi, T * (∫ z, ∏ i ∈ S, boundedHyperplaneFieldValue z (U i)
        ∂boundedHyperplaneFieldLaw d T) := by
  rw [finePairTimeSubsetMoment, finePairTimeFieldMeasure_integral d lo hi _
    (finePairTimeField_weighted_product_integrable lo hi U S)]
  simp only [finePairTimeFieldValue, integral_const_mul]

section Generic
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

theorem finePairPacket_even_subset_expansion {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => ∏ i, finePairDensityReset a b z eps p (ψ ζ) i) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient a b M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card *
          (∫ ζ, (∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  have hm (z eps : ℝ) (i : Fin n) :
      Measurable (fun ζ => finePairDensityReset a b z eps p (ψ ζ) i) := by
    unfold finePairDensityReset
    exact measurable_const.add ((hmψ i).const_mul _)
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => hm z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n) (fun ζ e =>
      finite_density_product_abs_bound _ b (ha.trans hab).le
        (fun i => finePairFieldReset_abs_le a b ha hab M p hp ψ hbψ (ζ,e) i))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have hiRsp : Integrable (fun ζ => responseMatrixAction q C (A ζ) c Φ) σ :=
    responseMatrixAction_integrable σ q C A (separatedMatrix_entry_integrable σ A hA hcost) c Φ
  have hi (W : Finset (Fin n)) :
      Integrable (fun ζ => (∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) σ := by
    apply hiRsp.bdd_mul (c := 1)
      (Finset.measurable_fun_prod W (fun i _ => hmψ i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hbψ ζ i)).trans_eq
        (Finset.prod_const_one)
  have hsubset (ζ : Z) :
      (∫ᵛ e, (∏ i, finePairDensityReset a b e.1 e.2 p (ψ ζ) i)
        ∂<•finePairDensitySignedRule a b M) =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient a b M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) *
          finePairEvenSelector W.card := by
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, finePairEvenSelector] using
      finePairDensitySignedRule_product_expansion a b M Finset.univ p (ψ ζ)
  simp_rw [hsubset]
  have he (W : Finset (Fin n)) (ζ : Z) :
      finePairCountCoefficient a b M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) *
        finePairEvenSelector W.card * responseMatrixAction q C (A ζ) c Φ =
      (finePairCountCoefficient a b M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card) *
        ((∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [Finset.sum_mul, he]
  rw [integral_finsetSum _ (fun W _ => (hi W).const_mul _)]
  simp only [integral_const_mul]

end Generic

theorem finePairFineFirstAction_even_subset_expansion {d n F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd T0 N M q C U p c Φ =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card *
          finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by
  rw [finePairFineFirstAction, finePairPacket_even_subset_expansion _ ad bd ha hab M q C _
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _)
    c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
    (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
    (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le)]
  apply Finset.sum_congr rfl
  intro W _
  change _ * (∫ e : ℝ × FinePairFieldMark d, (∏ i ∈ W, finePairTimeFieldValue e (U i)) *
    responseMatrixAction q C (fun i j => e.1 * finePairDistanceMatrix d F i j) c Φ
    ∂finePairTimeFieldMeasure d T0 N) = _
  simp_rw [responseMatrixAction_scalar_matrix]
  have he (e : ℝ × FinePairFieldMark d) :
      (∏ i ∈ W, finePairTimeFieldValue e (U i)) *
        (e.1 * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) =
      (e.1 * (∏ i ∈ W, finePairTimeFieldValue e (U i))) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by ring
  simp_rw [he]
  rw [integral_mul_const]
  unfold finePairTimeSubsetMoment
  ring

def finePairPairAliasAction {d n F : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
    finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * (if W.card = 2 then 1 else 0) *
      finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ

def finePairEvenFieldAction {d n F : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
    finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) *
      (if 4 ≤ W.card ∧ Even W.card then 1 else 0) *
        finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ

theorem finePairFineFirstAction_alias_even_field {d n F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd T0 N M q C U p c Φ =
      finePairPairAliasAction ad bd T0 N M q C U p c Φ +
        finePairEvenFieldAction ad bd T0 N M q C U p c Φ := by
  rw [finePairFineFirstAction_even_subset_expansion ad bd T0 N ha hab M q C U p hp c Φ]
  simp only [finePairEvenSelector_split, finePairPairAliasAction, finePairEvenFieldAction,
    mul_add, add_mul, Finset.sum_add_distrib]

theorem finePairPairAliasAction_zero_selected_count {d n F : ℕ}
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ)
    (hn : 3 ≤ n) (hM : n ≤ M) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairPairAliasAction ad bd T0 N M q C U p c Φ = 0 := by
  unfold finePairPairAliasAction
  apply Finset.sum_eq_zero
  intro W _
  by_cases hW : W.card = 2
  · rw [hW, finePairCountCoefficient_two_exact ad bd ha hab M n (by omega) hM]
    simp [show n ≠ 2 by omega]
  · simp [hW]

theorem finePairEvenFieldAction_zero_small_count {d n F : ℕ} (hn : n < 4)
    (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairEvenFieldAction ad bd T0 N M q C U p c Φ = 0 := by
  unfold finePairEvenFieldAction
  apply Finset.sum_eq_zero
  intro W hW
  have hc : W.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.mem_powerset.mp hW)
  simp [show ¬(4 ≤ W.card ∧ Even W.card) by omega]

end NearlyMinimax
