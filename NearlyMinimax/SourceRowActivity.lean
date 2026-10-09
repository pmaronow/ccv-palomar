module

public import NearlyMinimax.SourceRows


@[expose] public section

/-! Exact finite source activity bookkeeping, with costs derived from
the actual positive separated measures and signed atoms. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

theorem higherBandRowMass_le_activityCap_of_fine (d r m D q : ℕ) (hr : 2 ≤ r) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C lam L T : ℝ)
    (hT : 1 ≤ T) (fine : Bool) (hLT : fine = true → L ≤ T) :
    higherBandRowMass d r m D q a b C lam L T fine ≤ higherBandRowActivityCap d r m D q a b C lam T := by
  cases fine
  · exact higherBandRowMass_le_activityCap d r m D q hr hD a b ha hab C lam 1 T hT hT false
  · exact higherBandRowMass_le_activityCap d r m D q hr hD a b ha hab C lam L T hT (hLT rfl) true

def higherBandFilteredMass (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : ℝ :=
  if HigherBandFamilySelected d D M q a b C lam ℓ N μ i then
    higherBandRowMass d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
      a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2 else 0

def higherBandCoarseActivity (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (j : Fin (D-2)) : ℝ :=
  higherBandFilteredMass d D M q a b C lam ℓ N μ (j,false)

def higherBandFineActivity (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (j : Fin (D-2)) : ℝ :=
  higherBandFilteredMass d D M q a b C lam ℓ N μ (j,true)

theorem higherBandFilteredMass_nonneg (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : Fin (D-2) × Bool) :
    0 ≤ higherBandFilteredMass d D M q a b C lam ℓ N μ i := by
  unfold higherBandFilteredMass
  split_ifs
  · exact higherBandRowMass_nonneg d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
      a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2
  · rfl

theorem higherBandFilteredMass_le_cap (d D M q : ℕ) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C lam ℓ N μ : ℝ) (i : Fin (D-2) × Bool)
    (hT : 1 ≤ higherBandFamilyUpper d ℓ N μ i) :
    higherBandFilteredMass d D M q a b C lam ℓ N μ i ≤
      higherBandRowActivityCap d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
        a b C lam (higherBandFamilyUpper d ℓ N μ i) := by
  unfold higherBandFilteredMass
  split_ifs with hi
  · apply higherBandRowMass_le_activityCap_of_fine d _ _ D q (by dsimp [higherBandFamilyTarget]; omega)
      hD a b ha hab C lam ℓ _ hT i.2
    intro hf
    simpa [higherBandFamilyUpper, hf] using (hi.2.1 hf).le
  · unfold higherBandRowActivityCap ordinaryDensityActivityBase
    have hcap := higherBandInterpolationCap_nonneg d (higherBandFamilyTarget i) lam
      (higherBandFamilyUpper d ℓ N μ i) hT
    positivity

theorem higherBandFamily_totalMass_eq (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass =
      (∑ j : Fin (D-2), higherBandCoarseActivity d D M q a b C lam ℓ N μ j) +
      (∑ j : Fin (D-2), higherBandFineActivity d D M q a b C lam ℓ N μ j) := by
  classical
  change (∑ i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ,
    higherBandRowMass d (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q
      a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (HigherBandFamilySelected d D M q a b C lam ℓ N μ))
    (by intro i; simp) (fun i => higherBandRowMass d (higherBandFamilyTarget i)
      (higherBandFamilyGuardDegree M i) D q a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, higherBandCoarseActivity, higherBandFineActivity,
    higherBandFilteredMass, Finset.sum_add_distrib]
  exact add_comm _ _

theorem sourceRowTotalMass_eq (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass =
      highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass + singletonRowMass d D q a b C +
      highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass := by
  classical
  simp only [highRowTotalMass, Fintype.sum_sum_type, sourceRowData, sourceRowComponent,
    highUnionRowRestrict, Fintype.sum_unique, singletonRowData, higherBandFamilyData, add_assoc]

end NearlyMinimax
