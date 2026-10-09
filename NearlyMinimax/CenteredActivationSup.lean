module

public import NearlyMinimax.SourceActivationActivity


@[expose] public section

/-! The exact activation supremum in the centered-reference lemma.  The
upper bound is attained by a mark in a row of positive variation, including
when other row tags have zero mass. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

private theorem real_sSup_range_eq_of_attained {E : Type*} (f : E → ℝ) (B : ℝ)
    (hB : ∀ e, f e ≤ B) (e : E) (he : f e = B) :
    sSup (Set.range f) = B := by
  have hBound : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨e, rfl⟩; exact hB e⟩
  apply le_antisymm
  · exact csSup_le ⟨f e, ⟨e, rfl⟩⟩ (by rintro _ ⟨e, rfl⟩; exact hB e)
  · rw [← he]
    exact le_csSup hBound ⟨e, rfl⟩

/-- The actual absolute reference mark, followed by the one balancing branch,
has precisely the claimed activation supremum. -/
theorem balancedAbsoluteActivation_sSup {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w : E → ℝ) (hpos : 0 < signedMarkMass μ w)
    (δ : ℝ) (hδ : 0 < δ) :
    sSup (Set.range (fun e : E ⊕ Unit =>
      |balancedActivation (absoluteActivation μ w) δ e|)) = signedMarkMass μ w / δ := by
  obtain ⟨e, he⟩ := absoluteActivation_attains_mass μ w hpos
  apply real_sSup_range_eq_of_attained _ _
    (balancedActivation_bound _ δ _ hδ hpos.le (absoluteActivation_bound μ w)) (Sum.inl e)
  change |absoluteActivation μ w e / δ| = _
  rw [abs_div, abs_of_pos hδ, he]

/-- The mass in the exact supremum is the total variation of the genuine
signed density, rather than a supplied activation bound. -/
theorem balancedAbsoluteActivation_sSup_variation {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ)
    (hpos : 0 < signedMarkMass μ w) (δ : ℝ) (hδ : 0 < δ) :
    sSup (Set.range (fun e : E ⊕ Unit =>
      |balancedActivation (absoluteActivation μ w) δ e|)) =
      δ⁻¹ * ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [balancedAbsoluteActivation_sSup μ w hpos δ hδ,
    signedMarkMass_eq_variation μ w hw, div_eq_mul_inv]
  ring

section Rows
variable {I : Type*} [Fintype I] {E : I → Type*} [∀ i, MeasurableSpace (E i)]

omit [∀ i, MeasurableSpace (E i)] in
/-- Attainment only needs one row of positive mass; zero-mass row tags are
allowed in the source union. -/
theorem highCenteredRowUnionActivation_attains_bound_nonneg
    (B : I → ℝ) (hTotal : 0 < highRowTotalMass B)
    (w : (i : I) → E i → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (i : I) (hi : 0 < B i) (e : E i) (he : |w i e| = B i) :
    |highCenteredRowUnionActivation B w δ (Sum.inl ⟨i,e⟩)| = highRowTotalMass B / δ := by
  change |(w i e / (B i / highRowTotalMass B)) / δ| = _
  rw [abs_div, abs_div, abs_of_pos hδ, abs_of_pos (div_pos hi hTotal), he]
  field_simp [hi.ne', hTotal.ne']

theorem highCenteredRowUnionActivation_sSup_of_attainment
    (B : I → ℝ) (hB : ∀ i, 0 ≤ B i) (hTotal : 0 < highRowTotalMass B)
    (w : (i : I) → E i → ℝ) (hw : ∀ i e, |w i e| ≤ B i)
    (δ : ℝ) (hδ : 0 < δ) (i : I) (hi : 0 < B i)
    (e : E i) (he : |w i e| = B i) :
    sSup (Set.range (fun e : (Sigma E) ⊕ Unit =>
      |highCenteredRowUnionActivation B w δ e|)) = highRowTotalMass B / δ := by
  apply real_sSup_range_eq_of_attained _ _
    (balancedActivation_bound _ δ _ hδ hTotal.le
      (highRowUnionActivation_bound_nonneg B hB hTotal w hw)) (Sum.inl ⟨i,e⟩)
  exact highCenteredRowUnionActivation_attains_bound_nonneg B hTotal w δ hδ i hi e he

/-- A finite family of actual absolute signed-density references satisfies
the exact supremum identity, with no attainment hypothesis on its marks. -/
theorem highCenteredAbsoluteRowUnionActivation_sSup
    (μ : (i : I) → Measure (E i)) (w : (i : I) → E i → ℝ)
    (hTotal : 0 < highRowTotalMass (fun i => signedMarkMass (μ i) (w i)))
    (δ : ℝ) (hδ : 0 < δ) :
    sSup (Set.range (fun e : (Sigma E) ⊕ Unit =>
      |highCenteredRowUnionActivation (fun i => signedMarkMass (μ i) (w i))
        (fun i => absoluteActivation (μ i) (w i)) δ e|)) =
      highRowTotalMass (fun i => signedMarkMass (μ i) (w i)) / δ := by
  have hi : ∃ i, 0 < signedMarkMass (μ i) (w i) := by
    by_contra hn
    push Not at hn
    have hz : highRowTotalMass (fun i => signedMarkMass (μ i) (w i)) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i, hi⟩ := hi
  obtain ⟨e, he⟩ := absoluteActivation_attains_mass (μ i) (w i) hi
  exact highCenteredRowUnionActivation_sSup_of_attainment _
    (fun i => signedMarkMass_nonneg (μ i) (w i)) hTotal _
    (fun i => absoluteActivation_bound (μ i) (w i)) δ hδ i hi e he
end Rows

/-- The exact activation supremum for the complete, physically constructed
source row family.  The singleton row supplies a genuine attaining mark. -/
theorem sourceUnionActivation_sSup (d k D M q : ℕ) (hq : 1 ≤ q)
    (a b C lam ℓ N μ δ : ℝ) (ha : 0 < a) (hab : a < b) (hC : 0 < C) (hδ : 0 < δ) :
    sSup (Set.range (fun e : HighUnionMark (SourceRowMark d D M q a b C lam ℓ N μ) =>
      |highUnionActivation (sourceRowData d k D M q a b C lam ℓ N μ) δ e|)) =
      highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass / δ := by
  have hsingle := singletonRowMass_positive d D q hq a b ha hab C hC
  obtain ⟨e, he⟩ := absoluteActivation_attains_mass
    ((Measure.dirac () : Measure Unit).prod Measure.count)
    (highPacketMarkWeight a b D 1 D q C (fun _ : Unit => finePairUnitMatrix d D)) hsingle
  exact highCenteredRowUnionActivation_sSup_of_attainment _
    (sourceRowMass_nonneg d k D M q a b C lam ℓ N μ)
    (sourceRowTotalMass_positive d k D M q hq a b ha hab C hC lam ℓ N μ) _
    (sourceRowActivation_bound d k D M q a b C lam ℓ N μ) δ hδ
    (Sum.inr (Sum.inl ())) hsingle e he

/-- Literal centered-row normalization: C_ctr is the reciprocal of the
fixed source balancing fraction, and B_base is the actual sum of row TV. -/
theorem sourceUnionActivation_sSup_paper {d : ℕ} (K : ModelConstants d)
    (k D M q : ℕ) (hq : 1 ≤ q) (a b C lam ℓ N μ : ℝ)
    (ha : 0 < a) (hab : a < b) (hC : 0 < C) :
    sSup (Set.range (fun e : HighUnionMark (SourceRowMark d D M q a b C lam ℓ N μ) =>
      |highUnionActivation (sourceRowData d k D M q a b C lam ℓ N μ) (highCenterMix K) e|)) =
      (highCenterMix K)⁻¹ * highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass := by
  rw [sourceUnionActivation_sSup d k D M q hq a b C lam ℓ N μ
    (highCenterMix K) ha hab hC (highCenterMix_mem K).1, div_eq_mul_inv]
  ring

end NearlyMinimax
