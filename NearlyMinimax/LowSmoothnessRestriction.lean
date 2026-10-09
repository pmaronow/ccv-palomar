module

public import NearlyMinimax.LowSmoothnessPrior


@[expose] public section

/-! Exact restriction of actual patch scores to their observed support.
The resulting estimates depend on the actual patch count, while regression
values and weights may depend arbitrarily on the observed design tuple. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

private theorem patch_variance_ratio' (n : ℕ) (a V η z : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchVarianceTerm n a V η g w y z i / patchResponseProduct n a V η g w y z =
      ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i) := by
  unfold patchVarianceTerm patchResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_div_mul_right _ _ (ne_of_gt (Finset.prod_pos (fun k _ => hp k)))

theorem patch_score_ratio_formula (n : ℕ) (a V η z : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchObservableScore n a V η g w y z =
      symmetricDifference (patchResponseProduct n a V η g w y) /
        patchResponseProduct n a V η g w y z -
      η ^ 2 * ∑ i, (w i) ^ 2 *
        (ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i)) := by
  unfold patchObservableScore patchScoreNumerator
  rw [sub_div]
  simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, patch_variance_ratio' n a V η z g w y _ hp]

/-- Exact restriction to the patch, under any enumeration of its observation indices. -/
theorem patch_score_restrict (n k : ℕ) (a V η z : ℝ) (g w : Fin n → ℝ)
    (S : Finset (Fin n)) (e : Fin k ≃ S) (hw : ∀ i, i ∉ S → w i = 0)
    (y : Fin n → Fin 3)
    (hp : ∀ i, 0 < ternaryMass a (g i + η * w i * z) V (y i)) :
    patchObservableScore n a V η g w y z =
      patchObservableScore k a V η (fun i => g (e i)) (fun i => w (e i))
        (fun i => y (e i)) z := by
  let O : ℝ := ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (y i)
  have hO : O ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    simpa [hw i (Finset.mem_sdiff.mp hi).2] using hp i
  have hfactor (u : ℝ) : patchResponseProduct n a V η g w y u =
      O * patchResponseProduct k a V η (fun i => g (e i)) (fun i => w (e i))
        (fun i => y (e i)) u := by
    unfold patchResponseProduct
    rw [← Finset.prod_sdiff (Finset.subset_univ S)]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp [hw i (Finset.mem_sdiff.mp hi).2]
    · rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
      exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hratio (u : ℝ) : patchResponseProduct n a V η g w y u /
      patchResponseProduct n a V η g w y z =
      patchResponseProduct k a V η (fun i => g (e i)) (fun i => w (e i))
        (fun i => y (e i)) u /
      patchResponseProduct k a V η (fun i => g (e i)) (fun i => w (e i))
        (fun i => y (e i)) z := by
    rw [hfactor u, hfactor z]
    exact mul_div_mul_left _ _ hO
  rw [patch_score_ratio_formula n a V η z g w y hp,
    patch_score_ratio_formula k a V η z _ _ _ (fun i => hp (e i))]
  congr 1
  · unfold symmetricDifference
    simp only [sub_div, add_div, mul_div_assoc]
    rw [hratio 1, hratio (-1), hratio 0]
  · congr 1
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
      exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    · intro i _ hi
      simp [hw i hi]

/-- The full patch score vanishes when its actual observed support has size at most one. -/
theorem patch_score_zero_of_support_count_lt_two (n : ℕ) (a V η z : ℝ)
    (g w : Fin n → ℝ) (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y : Fin n → Fin 3) (ha : a ≠ 0) (hcount : S.card < 2) :
    patchObservableScore n a V η g w y z = 0 := by
  have hcases : S.card = 0 ∨ S.card = 1 := by omega
  rcases hcases with hzero | hone
  · have hS : S = ∅ := Finset.card_eq_zero.mp hzero
    have hnum := patch_score_cancel_zero n a V η g w y z (fun i => hw i (by simp [hS]))
    simp [patchObservableScore, hnum]
  · obtain ⟨i, hS⟩ := Finset.card_eq_one.mp hone
    have hnum := patch_score_cancel_singleton n a V η g w y z ha i
      (fun k hki => hw k (by simpa [hS] using hki))
    simp [patchObservableScore, hnum]

/-- Actual full-response score bound with the size of its observed support.
The field and weights may be any functions of the design tuple. -/
theorem patch_score_square_support_bound (n : ℕ) (a V η z ρ c : ℝ)
    (g w : Fin n → ℝ) (S : Finset (Fin n)) (y : Fin n → Fin 3)
    (hcount : 1 ≤ S.card) (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hz : z ∈ Icc (-1 : ℝ) 1) (hwzero : ∀ i, i ∉ S → w i = 0)
    (hw : ∀ i ∈ S, |w i| ≤ 1)
    (hreg : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S, |g i + η * w i * u| ≤ ρ)
    (hq : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S,
      0 ≤ ternaryMass a (g i + η * w i * u) V (y i) ∧
        ternaryMass a (g i + η * w i * u) V (y i) ≤ 1)
    (hlower : ∀ i ∈ S, c ≤ ternaryMass a (g i + η * w i * z) V (y i))
    (hp : ∀ i, 0 < ternaryMass a (g i + η * w i * z) V (y i)) :
    (patchObservableScore n a V η g w y z) ^ 2 ≤
      ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4 := by
  let e := S.equivFin.symm
  rw [patch_score_restrict n S.card a V η z g w S e hwzero y hp]
  let M := (2 * ρ + a) / a ^ 2
  let K := M ^ 2 + 3 / a ^ 2
  have hs := patch_score_square_bound S.card a V η z M (2 / a ^ 2) (1 / a ^ 2) c
    (fun i => g (e i)) (fun i => w (e i)) (fun i => y (e i)) hcount hz
    (by dsimp [M]; positivity) (by positivity) (by positivity) hc
    (fun i => hw (e i) (e i).property)
    (fun u hu i => (abs_of_nonneg (hq u hu (e i) (e i).property).1).trans_le
      (hq u hu (e i) (e i).property).2)
    (fun u hu i => ternary_mean_derivative_abs_bound a _ ρ ha hρ
      (hreg u hu (e i) (e i).property) (y (e i)))
    (fun i => ternary_mean_second_derivative_abs_bound a ha (y (e i)))
    (fun i => ternary_variance_derivative_abs_bound a ha (y (e i)))
    (fun i => hlower (e i) (e i).property)
  have hK : M ^ 2 + 2 / a ^ 2 + 1 / a ^ 2 = K := by dsimp [K]; ring
  rw [hK] at hs
  simpa [ternaryScoreExponentialConstant, K, M] using
    score_bound_exponential_absorption S.card K c η _ hcount hc hs

/-- Genuine full conditional response energy has the collision envelope,
with the actual support count rather than an assumed restricted experiment. -/
theorem patch_expected_score_energy_support_bound (n : ℕ) (a V η z ρ c : ℝ)
    (g w : Fin n → ℝ) (S : Finset (Fin n))
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hz : z ∈ Icc (-1 : ℝ) 1) (hwzero : ∀ i, i ∉ S → w i = 0)
    (hw : ∀ i ∈ S, |w i| ≤ 1)
    (hreg : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S, |g i + η * w i * u| ≤ ρ)
    (hq : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S, ∀ y,
      0 ≤ ternaryMass a (g i + η * w i * u) V y ∧
        ternaryMass a (g i + η * w i * u) V y ≤ 1)
    (hlower : ∀ i ∈ S, ∀ y, c ≤ ternaryMass a (g i + η * w i * z) V y)
    (hp : ∀ i y, 0 < ternaryMass a (g i + η * w i * z) V y) :
    patchExpectedScoreEnergy n a V η g w z ≤
      if 2 ≤ S.card then ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4 else 0 := by
  unfold patchExpectedScoreEnergy
  split_ifs with hcount
  · calc
      _ ≤ ∑ y : Fin n → Fin 3, patchResponseProduct n a V η g w y z *
          (ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4) := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left
          (patch_score_square_support_bound n a V η z ρ c g w S y (by omega)
            ha hρ hc hz hwzero hw hreg (fun u hu i hi => hq u hu i hi (y i))
            (fun i hi => hlower i hi (y i)) (fun i => hp i (y i)))
          (Finset.prod_nonneg (fun i _ => (hp i (y i)).le))
      _ = _ := by rw [← Finset.sum_mul, patch_response_normalized n a V η g w z ha.ne', one_mul]
  · have hlt : S.card < 2 := by omega
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    rw [patch_score_zero_of_support_count_lt_two n a V η z g w S hwzero y ha.ne' hlt]
    ring

theorem patch_expected_score_energy_measurable {α : Type*} [MeasurableSpace α]
    (n : ℕ) (a V η z : ℝ) (g w : α → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun x => g x i)) (hw : ∀ i, Measurable (fun x => w x i)) :
    Measurable (fun x => patchExpectedScoreEnergy n a V η (g x) (w x) z) := by
  have hq (u : ℝ) (i : Fin n) (y : Fin 3) :
      Measurable (fun x => ternaryMass a (g x i + η * w x i * u) V y) := by
    apply ternaryMass_measurable_comp
    fun_prop
  have hprod (s : Finset (Fin n)) (u : ℝ) (y : Fin n → Fin 3) :
      Measurable (fun x => ∏ i ∈ s, ternaryMass a (g x i + η * w x i * u) V (y i)) :=
    Finset.measurable_prod _ (fun i _ => hq u i (y i))
  have hpatch (u : ℝ) (y : Fin n → Fin 3) :
      Measurable (fun x => patchResponseProduct n a V η (g x) (w x) y u) := hprod _ u y
  have hvar (i : Fin n) (y : Fin n → Fin 3) :
      Measurable (fun x => patchVarianceTerm n a V η (g x) (w x) y z i) :=
    (hprod (Finset.univ.erase i) z y).const_mul _
  have hscore (y : Fin n → Fin 3) :
      Measurable (fun x => patchObservableScore n a V η (g x) (w x) y z) := by
    have hcorr : Measurable (fun x => ∑ i, (w x i) ^ 2 *
        patchVarianceTerm n a V η (g x) (w x) y z i) :=
      Finset.measurable_sum _ (fun i _ => (hw i).pow_const 2 |>.mul (hvar i y))
    exact (((hpatch 1 y).const_mul (1 / 2) |>.add ((hpatch (-1) y).const_mul (1 / 2))
      |>.sub (hpatch 0 y)).sub (hcorr.const_mul (η ^ 2))).div (hpatch z y)
  exact Finset.measurable_sum _ (fun y _ => (hpatch z y).mul ((hscore y).pow_const 2))

/-- Every function of the actual bounded design count is integrable. -/
theorem iid_design_count_observable_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (e : ℕ → ℝ) :
    Integrable (fun x : Fin n → α => e (designPatchCount n A x))
      (Measure.pi (fun _ : Fin n => μ)) := by
  apply Integrable.of_bound
    ((measurable_of_countable e).comp (design_patch_count_measurable n A hA)).aestronglyMeasurable
    (∑ k ∈ Finset.range (n + 1), |e k|)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun k => |e k|) (fun k _ => abs_nonneg (e k))
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (design_patch_count_le n A x)))

/-- The actual full conditional response energy, integrated over a genuine
IID design, satisfies the collision bound even when all fields depend on
the complete observed design tuple. -/
theorem iid_design_full_patch_score_energy_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (a V η z ρ c : ℝ) (g w : (Fin n → α) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun x => g x i)) (hwmeas : ∀ i, Measurable (fun x => w x i))
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c) (hz : z ∈ Icc (-1 : ℝ) 1)
    (hmean : n * μ.real A ≤ 1)
    (hwzero : ∀ x i, x i ∉ A → w x i = 0)
    (hw : ∀ x i, x i ∈ A → |w x i| ≤ 1)
    (hreg : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i, x i ∈ A → |g x i + η * w x i * u| ≤ ρ)
    (hq : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i, x i ∈ A → ∀ y,
      0 ≤ ternaryMass a (g x i + η * w x i * u) V y ∧
        ternaryMass a (g x i + η * w x i * u) V y ≤ 1)
    (hlower : ∀ x i, x i ∈ A → ∀ y, c ≤ ternaryMass a (g x i + η * w x i * z) V y)
    (hp : ∀ x i y, 0 < ternaryMass a (g x i + η * w x i * z) V y) :
    (∫ x : Fin n → α, patchExpectedScoreEnergy n a V η (g x) (w x) z
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ternaryScoreExponentialConstant a ρ c ^ 2 * Real.exp (ternaryScoreExponentialConstant a ρ c) *
        η ^ 4 * (n * μ.real A) ^ 2 := by
  let K := ternaryScoreExponentialConstant a ρ c
  let e : ℕ → ℝ := fun k => if 2 ≤ k then K ^ k * η ^ 4 else 0
  have hK : 0 ≤ K := by dsimp [K, ternaryScoreExponentialConstant]; positivity
  have hpoint (x : Fin n → α) : patchExpectedScoreEnergy n a V η (g x) (w x) z ≤
      e (designPatchCount n A x) := by
    let S := Finset.univ.filter (fun i : Fin n => x i ∈ A)
    have hS (i : Fin n) : i ∈ S ↔ x i ∈ A := by simp [S]
    exact patch_expected_score_energy_support_bound n a V η z ρ c (g x) (w x) S ha hρ hc hz
      (fun i hi => hwzero x i (fun h => hi ((hS i).mpr h)))
      (fun i hi => hw x i ((hS i).mp hi))
      (fun u hu i hi => hreg x u hu i ((hS i).mp hi))
      (fun u hu i hi y => hq x u hu i ((hS i).mp hi) y)
      (fun i hi y => hlower x i ((hS i).mp hi) y) (hp x)
  have he := iid_design_count_observable_integrable μ n A hA e
  have henergy : Integrable (fun x => patchExpectedScoreEnergy n a V η (g x) (w x) z)
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply he.mono' (patch_expected_score_energy_measurable n a V η z g w hg hwmeas).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint x
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg
        (Finset.prod_nonneg (fun i _ => (hp x i (y i)).le)) (sq_nonneg _))
  exact (integral_mono henergy he hpoint).trans
    (iid_design_collision_energy_bound μ n A hA K η e hK hmean (by simp [e])
      (by simp [e]) (fun k hk => by simp [e, hk]))

/-- Uniform legal fields make their actual conditional response energies
integrable; no energy or integrability conclusion is assumed. -/
theorem patch_expected_score_energy_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) (a V η z ρ c : ℝ) (g w : α → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun x => g x i)) (hwmeas : ∀ i, Measurable (fun x => w x i))
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c) (hz : z ∈ Icc (-1 : ℝ) 1)
    (hw : ∀ x i, |w x i| ≤ 1)
    (hreg : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i, |g x i + η * w x i * u| ≤ ρ)
    (hq : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i y,
      0 ≤ ternaryMass a (g x i + η * w x i * u) V y ∧
        ternaryMass a (g x i + η * w x i * u) V y ≤ 1)
    (hlower : ∀ x i y, c ≤ ternaryMass a (g x i + η * w x i * z) V y) :
    Integrable (fun x => patchExpectedScoreEnergy n a V η (g x) (w x) z) μ := by
  cases n with
  | zero =>
    simp_rw [patch_expected_score_energy_zero]
    exact integrable_zero _ _ _
  | succ n =>
    apply Integrable.of_bound
      (patch_expected_score_energy_measurable (n + 1) a V η z g w hg hwmeas).aestronglyMeasurable
      (ternaryScoreExponentialConstant a ρ c ^ (n + 1) * η ^ 4)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact patch_expected_score_energy_bound (n + 1) a V η z ρ c (g x) (w x) (by omega)
        ha hρ hc hz (hw x) (hreg x) (hq x) (hlower x)
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg
        (Finset.prod_nonneg (fun i _ => (hq x z hz i (y i)).1)) (sq_nonneg _))

end NearlyMinimax
