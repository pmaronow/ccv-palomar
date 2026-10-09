module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.SingletonRow
public import NearlyMinimax.FinePairRowNondegenerate


@[expose] public section

/-! The complete finite source row family: singleton, three genuine pair
rows, and all selected ordinary higher-target coarse/fine bands. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def highUnionRowRestrict {d k D : ℕ} {I : Type*} {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (R : HighUnionRowData d k D I E) (i : I) : HighUnionRowData d k D Unit (fun _ => E i) where
  rowLaw := fun _ => R.rowLaw i
  rowMass := fun _ => R.rowMass i
  rowActivation := fun _ => R.rowActivation i
  rowIntercept := fun _ => R.rowIntercept i
  rowSlope := fun j _ => R.rowSlope j i
  rowVector := fun _ => R.rowVector i
  rowTime := fun _ => R.rowTime i

abbrev SourceRowIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  FinePairRowTag ⊕ (Unit ⊕ HigherBandFamilyIndex d D M q a b C lam ℓ N μ)

def SourceRowMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowMark d D M q p
  | .inr (.inl _) => SingletonRowMark d D q
  | .inr (.inr i) => HigherBandFamilyMark d D M q a b C lam ℓ N μ i

instance sourceRowMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : MeasurableSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_measurable d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark] <;> infer_instance

instance sourceRowMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : StandardBorelSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_standardBorel d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark, sourceRowMark_measurable] <;> infer_instance

def sourceRowComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      HighUnionRowData d k D Unit (fun _ => SourceRowMark d D M q a b C lam ℓ N μ i)
  | .inl p => highUnionRowRestrict (finePairRowData d k D M q a b C ℓ N) p
  | .inr (.inl _) => singletonRowData d k D q a b C
  | .inr (.inr i) => higherBandFamilyComponent d k D M q a b C lam ℓ N μ i

def sourceRowData (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    HighUnionRowData d k D (SourceRowIndex d D M q a b C lam ℓ N μ)
      (SourceRowMark d D M q a b C lam ℓ N μ) where
  rowLaw := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowLaw ()
  rowMass := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowMass ()
  rowActivation := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowActivation ()
  rowIntercept := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowIntercept ()
  rowSlope := fun j i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowSlope j ()
  rowVector := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowVector ()
  rowTime := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowTime ()

theorem sourceRowMass_nonneg (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    0 ≤ (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p => exact finePairRowMass_nonneg d D M q a b C ℓ N p
  | inr i =>
    cases i with
    | inl _ => exact signedMarkMass_nonneg _ _
    | inr i => exact (higherBandFamily_mass_positive d k D M q a b C lam ℓ N μ i).le

theorem sourceRowTotalMass_positive (d k D M q : ℕ) (hq : 1 ≤ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) (hC : 0 < C) (lam ℓ N μ : ℝ) :
    0 < highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass := by
  apply (singletonRowMass_positive d D q hq a b ha hab C hC).trans_le
  exact Finset.single_le_sum (fun i _ => sourceRowMass_nonneg d k D M q a b C lam ℓ N μ i)
    (Finset.mem_univ (Sum.inr (Sum.inl ())))

theorem sourceRow_probability (d : ℕ) [NeZero d] (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) (hC : 0 < C)
    (lam ℓ N μ : ℝ) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    IsProbabilityMeasure ((sourceRowData d k D M q a b C lam ℓ N μ).rowLaw i) := by
  cases i with
  | inl p => exact finePairRowLaw_probability_actual d D hD M q hq a b ha hab C hC ℓ N hℓ hℓN p
  | inr i =>
    cases i with
    | inl _ => exact singletonRow_probability d k D q hq a b ha hab C hC
    | inr i => exact higherBandFamily_probability d k D M q a b C lam ℓ N μ i

end NearlyMinimax
