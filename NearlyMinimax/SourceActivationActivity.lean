module

public import NearlyMinimax.SourceSaddleActivity


@[expose] public section

/-! The genuine one-dummy global activation bound, including zero-mass
row tags, specialized to the complete source family. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

section Generic
variable {I : Type*} [Fintype I] {E : I → Type*} [∀ i, MeasurableSpace (E i)]

theorem highRowUnionActivation_bound_nonneg (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hTotal : 0 < highRowTotalMass B) (w : (i : I) → E i → ℝ)
    (hw : ∀ i e, |w i e| ≤ B i) (e : Sigma E) :
    |highRowUnionActivation B w e| ≤ highRowTotalMass B := by
  by_cases hz : B e.1 = 0
  · simpa only [highRowUnionActivation, highRowSelectionProbability, hz, zero_div, div_zero, abs_zero] using hTotal.le
  · have hp : 0 < B e.1 := lt_of_le_of_ne (hB e.1) (Ne.symm hz)
    have hprob : 0 < highRowSelectionProbability B e.1 := div_pos hp hTotal
    unfold highRowUnionActivation
    rw [abs_div, abs_of_pos hprob]
    apply (div_le_iff₀ hprob).mpr
    have he : highRowTotalMass B * highRowSelectionProbability B e.1 = B e.1 := by
      unfold highRowSelectionProbability
      field_simp
    rw [he]
    exact hw e.1 e.2

theorem highUnionActivation_bound_nonneg {d k F : ℕ} (R : HighUnionRowData d k F I E)
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (hw : ∀ i e, |R.rowActivation i e| ≤ R.rowMass i)
    (δ : ℝ) (hδ : 0 < δ) (e : HighUnionMark E) :
    |highUnionActivation R δ e| ≤ highRowTotalMass R.rowMass / δ :=
  balancedActivation_bound _ δ _ hδ hTotal.le
    (highRowUnionActivation_bound_nonneg R.rowMass hMass hTotal R.rowActivation hw) e
end Generic

theorem sourceRowActivation_bound (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (e : SourceRowMark d D M q a b C lam ℓ N μ i) :
    |(sourceRowData d k D M q a b C lam ℓ N μ).rowActivation i e| ≤
      (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i := by
  cases i with
  | inl i => exact finePairRowActivation_bound d D M q a b C ℓ N i e
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacketActivation_bound (Measure.dirac () : Measure Unit) a b D 1 D q C
        (fun _ : Unit => finePairUnitMatrix d D) e
    | inr i =>
      exact higherBandRowActivation_bound d (higherBandFamilyTarget i.val)
        (higherBandFamilyGuardDegree M i.val) D q a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2 e

theorem sourceUnionActivation_bound (d k D M q : ℕ) (hq : 1 ≤ q)
    (a b C lam ℓ N μ δ : ℝ) (ha : 0 < a) (hab : a < b) (hC : 0 < C) (hδ : 0 < δ)
    (e : HighUnionMark (SourceRowMark d D M q a b C lam ℓ N μ)) :
    |highUnionActivation (sourceRowData d k D M q a b C lam ℓ N μ) δ e| ≤
      highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass / δ :=
  highUnionActivation_bound_nonneg _ (sourceRowMass_nonneg d k D M q a b C lam ℓ N μ)
    (sourceRowTotalMass_positive d k D M q hq a b ha hab C hC lam ℓ N μ)
    (sourceRowActivation_bound d k D M q a b C lam ℓ N μ) δ hδ e

end NearlyMinimax
