module

public import NearlyMinimax.AtomicRules


@[expose] public section

/-! Total variation and support of the finite signed rules. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators ENNReal
open MeasureTheory VectorMeasure

section Atomic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]

theorem atomicVariationBound_total (z : ι → X) (w : ι → ℝ) :
    atomicVariationBound z w Set.univ = ∑ i, ‖w i‖ₑ := by
  simp [atomicVariationBound, Measure.finsetSum_apply, enorm_eq_nnnorm]

theorem atomicSignedRule_totalVariation_le (z : ι → X) (w : ι → ℝ) :
    ((atomicSignedRule z w).variation Set.univ).toReal ≤ ∑ i, |w i| := by
  have h := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at h
  have hfin : (∑ i, ‖w i‖ₑ) ≠ ∞ := by simp
  apply (ENNReal.toReal_mono hfin h).trans_eq
  rw [ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp

theorem atomicSignedRule_variation_outside (z : ι → X) (w : ι → ℝ)
    (B : Set X) (hB : MeasurableSet B) (hz : ∀ i, z i ∈ B) :
    (atomicSignedRule z w).variation Bᶜ = 0 := by
  apply le_antisymm _ (by exact zero_le)
  apply (Measure.le_iff.1 (atomicSignedRule_variation_le z w) Bᶜ hB.compl).trans
  simp [atomicVariationBound, Measure.finsetSum_apply, Measure.dirac_apply', hz]

theorem atomicSignedRule_singleton (z : ι → X) (w : ι → ℝ)
    (hz : Function.Injective z) (i : ι) : atomicSignedRule z w {z i} = w i := by
  classical
  rw [atomicSignedRule, VectorMeasure.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    exact VectorMeasure.dirac_apply_of_notMem (by simpa using hz.ne hji)
  · simp

/-- Distinct atoms give equality of the actual total variation and the atom-weight sum. -/
theorem atomicSignedRule_totalVariation_eq (z : ι → X) (w : ι → ℝ)
    (hz : Function.Injective z) :
    ((atomicSignedRule z w).variation Set.univ).toReal = ∑ i, |w i| := by
  classical
  have hsingleton (i : ι) : (atomicSignedRule z w).variation {z i} = ‖w i‖ₑ := by
    rw [VectorMeasure.variation_apply_singleton, atomicSignedRule_singleton z w hz i]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i => ({z i} : Set X)) := by
    intro i hi j hj hij
    exact Set.disjoint_singleton.mpr (hz.ne hij)
  have hsum := measure_biUnion_finset (μ := (atomicSignedRule z w).variation)
    hdisj (fun i hi => measurableSet_singleton (z i))
  have hlower : (∑ i, ‖w i‖ₑ) ≤ (atomicSignedRule z w).variation Set.univ := by
    simp_rw [hsingleton] at hsum
    rw [← hsum]
    exact measure_mono (Set.subset_univ _)
  have hupper := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at hupper
  have he := le_antisymm hupper hlower
  rw [he, ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp

theorem atomicSignedRule_variation_eq (z : ι → X) (w : ι → ℝ)
    (hz : Function.Injective z) : (atomicSignedRule z w).variation = atomicVariationBound z w := by
  apply Measure.eq_of_le_of_measure_univ_eq (atomicSignedRule_variation_le z w)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [atomicSignedRule_totalVariation_eq z w hz, atomicVariationBound_total,
    ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp

theorem atomicVariationBound_reflection (z : ι → X) (w : ι → ℝ)
    (e : ι ≃ ι) (R : X → X) (hz : ∀ i, z (e i) = R (z i))
    (hw : ∀ i, ‖w (e i)‖₊ = ‖w i‖₊) (B : Set X) :
    atomicVariationBound z w (R ⁻¹' B) = atomicVariationBound z w B := by
  simp only [atomicVariationBound, Measure.finsetSum_apply, Measure.smul_apply]
  apply Fintype.sum_equiv e
  intro i
  rw [hw i, hz i]
  by_cases hi : R (z i) ∈ B <;> simp [Measure.dirac_apply, hi]

end Atomic

theorem exteriorSignedRule_totalVariation (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (n : ℕ) (hn : 1 ≤ n) :
    ((exteriorSignedRule a b n).variation Set.univ).toReal =
      Real.cosh ((n : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [exteriorSignedRule, atomicSignedRule_totalVariation_eq _ _
    (exteriorNode_strictAnti a b hab n hn).injective]
  exact exterior_rule_variation a b ha hab n hn

theorem derivativeSignedRule_totalVariation (D : ℕ) (hD : 1 ≤ D) :
    ((derivativeSignedRule D).variation Set.univ).toReal = derivativeOrder D := by
  unfold derivativeSignedRule
  rw [atomicSignedRule_totalVariation_eq _ _
    (lobattoNode_strictAnti (2 * ((D - 1) / 2) + 1) (by omega)).injective]
  exact lobatto_derivative_rule_variation ((D - 1) / 2)

/-- Reflection leaves the actual total-variation measure of the derivative rule invariant. -/
theorem derivativeSignedRule_variation_symmetric (D : ℕ) (B : Set ℝ) :
    (derivativeSignedRule D).variation ((fun z : ℝ => -z) ⁻¹' B) =
      (derivativeSignedRule D).variation B := by
  unfold derivativeSignedRule
  rw [atomicSignedRule_variation_eq _ _
    (lobattoNode_strictAnti (2 * ((D - 1) / 2) + 1) (by omega)).injective]
  apply atomicVariationBound_reflection _ _ Fin.revPerm (fun z : ℝ => -z)
  · exact lobattoNode_reflection _ (by omega)
  · intro i
    rw [show Fin.revPerm i = i.rev by rfl, lobattoDerivativeWeight_reflection]
    simp

/-- The response rule has fixed finite variation depending only on its fixed order `q`. -/
theorem responseSignedRule_totalVariation (q : ℕ) :
    ((responseSignedRule q).variation Set.univ).toReal =
      ∑ j : Fin (2 * q + 2), |responseWeight q j| := by
  exact atomicSignedRule_totalVariation_eq _ _ (responseNode_injective q)

section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Together with weight additivity, scalar homogeneity gives the paper's linear dependence on `A`. -/
theorem covarianceWeight_smul (C t : ℝ) (A : ι → ι → ℝ) (i j : ι) (s u : Bool) :
    covarianceWeight C (fun k l => t * A k l) i j s u = t * covarianceWeight C A i j s u := by
  unfold covarianceWeight
  ring

/-- The fixed four-sign covariance kernel, as an actual signed measure. -/
def covarianceSignedRule (C : ℝ) (A : ι → ι → ℝ) : SignedMeasure (ι → ℝ) :=
  atomicSignedRule
    (fun x : ι × ι × Bool × Bool => covarianceAtom C x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x : ι × ι × Bool × Bool => covarianceWeight C A x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem covarianceSignedRule_integral (C : ℝ) (A : ι → ι → ℝ) (f : (ι → ℝ) → ℝ) :
    ∫ᵛ v, f v ∂<•(covarianceSignedRule C A) = covarianceAction C A f := by
  rw [covarianceSignedRule, atomicSignedRule_integral]
  simp only [Fintype.sum_prod_type, covarianceAction]

theorem covarianceSignedRule_zero_mass (C : ℝ) (A : ι → ι → ℝ) :
    ∫ᵛ v, (1 : ℝ) ∂<•(covarianceSignedRule C A) = 0 := by
  rw [covarianceSignedRule_integral]
  exact covariance_zero_mass C A

theorem covarianceSignedRule_zero_mean (C : ℝ) (A : ι → ι → ℝ) (k : ι) :
    ∫ᵛ v, v k ∂<•(covarianceSignedRule C A) = 0 := by
  rw [covarianceSignedRule_integral]
  exact covariance_zero_mean C A k

theorem covarianceSignedRule_second_moment (C : ℝ) (A : ι → ι → ℝ) (hC : C ≠ 0)
    (hA : ∀ k l, A k l = A l k) (k l : ι) :
    ∫ᵛ v, v k * v l ∂<•(covarianceSignedRule C A) = A k l := by
  rw [covarianceSignedRule_integral]
  exact covariance_second_moment_symmetric C A hC hA k l

theorem covarianceSignedRule_totalVariation_le (C : ℝ) (A : ι → ι → ℝ) :
    ((covarianceSignedRule C A).variation Set.univ).toReal ≤ 2 * C ^ 2 * ∑ i, ∑ j, |A i j| := by
  apply (atomicSignedRule_totalVariation_le _ _).trans_eq
  simp only [Fintype.sum_prod_type]
  exact covariance_weight_variation C A

/-- Actual total variation outside the coefficient ball is zero. -/
theorem covarianceSignedRule_supported (C : ℝ) (hC : 0 < C) (A : ι → ι → ℝ) :
    (covarianceSignedRule C A).variation {v : ι → ℝ | ∑ k, |v k| ≤ 1 / C}ᶜ = 0 := by
  apply atomicSignedRule_variation_outside
  · exact measurableSet_le (by fun_prop) measurable_const
  · intro x
    simpa only [Set.mem_setOf_eq, one_div] using covarianceAtom_mem_ball C hC x.1 x.2.1 x.2.2.1 x.2.2.2

/-- Fixed atoms give pointwise measurability of the signed covariance kernel in its matrix argument. -/
theorem covarianceSignedRule_measurable (C : ℝ) (S : Set (ι → ℝ)) (hS : MeasurableSet S) :
    Measurable (fun A : ι → ι → ℝ => covarianceSignedRule C A S) := by
  unfold covarianceSignedRule atomicSignedRule
  simp only [FunLike.coe_sum, Finset.sum_apply]
  apply Finset.measurable_sum
  intro x hx
  by_cases hmem : covarianceAtom C x.1 x.2.1 x.2.2.1 x.2.2.2 ∈ S
  · simp only [VectorMeasure.dirac_apply_of_mem hS hmem]
    unfold covarianceWeight
    fun_prop
  · simp only [VectorMeasure.dirac_apply_of_notMem hmem]
    exact measurable_const

end Covariance
end NearlyMinimax
