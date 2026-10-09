module

public import NearlyMinimax.HigherBandFamily


@[expose] public section

/-! Exact omission of zero-variation rows and positive subunit scale rows
from the actual finite signed family. A subunit interpolation target remains
zero; no zero-defect assertion is made for that source branch. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

theorem centered_cardinal_measure_below_one_eq_zero {n : ℕ} (i : Fin n) (d : ℕ)
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1) : centeredCardinalMeasure i d T = 0 := by
  simp only [centeredCardinalMeasure, spatialScaleMeasure,
    spatial_scale_domain_empty_below_one i hT hT1, Measure.restrict_empty, Measure.zero_prod]

theorem cardinal_separated_measure_below_one_eq_zero (d n : ℕ) {T : ℝ}
    (hT : 0 < T) (hT1 : T < 1) : cardinalSeparatedMeasure d n T = 0 := by
  unfold cardinalSeparatedMeasure
  simp_rw [centered_cardinal_measure_below_one_eq_zero _ d hT hT1, Measure.map_zero]
  exact Finset.sum_const_zero

theorem higherBand_coarse_below_one_signed_zero (d r m D q : ℕ) (a b C lam L T : ℝ)
    (hT : 0 < T) (hT1 : T < 1) : higherBandSignedRow d r m D q a b C lam L T false = 0 := by
  rw [higherBandSignedRow, higherBandCarrierMeasure,
    cardinal_separated_measure_below_one_eq_zero d r hT hT1, highPacketSignedMeasure, Measure.zero_prod]
  ext1 s hs
  rw [withDensityᵥ_apply (by simp : Integrable _ (0 : Measure _)) hs]
  simp

def higherBandFamilyRowIntegral (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  ∫ᵛ e, F i e ∂<•higherBandSignedRow d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
    a b C lam ell (higherBandFamilyUpper d ell N mu i) i.2

def higherBandPhysicalIntegral (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 = true then
    if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
      higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i else 0
  else higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i

theorem higherBandPhysicalIntegral_selected (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) (hi : HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral d D M q a b C lam ell N mu F i =
      higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i := by
  unfold higherBandPhysicalIntegral
  by_cases hf : i.2 = true
  · rw [ite_eq_left hf, ite_eq_left (hi.2.1 hf)]
  · rw [ite_eq_right hf]

theorem higherBandPhysicalIntegral_unselected_zero (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) (hi : ¬HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral d D M q a b C lam ell N mu F i = 0 := by
  rcases i with ⟨j, fine⟩
  cases fine
  · simp only [higherBandPhysicalIntegral, Bool.false_eq_true, ite_false]
    have hT : 0 < min ell (higherBandTargetScale d (j.val+3) N mu) :=
      lt_min (by linarith) (hnu j)
    by_cases hT1 : 1 ≤ min ell (higherBandTargetScale d (j.val+3) N mu)
    · have hz : higherBandRowMass d (j.val+3) D D q a b C lam ell
          (min ell (higherBandTargetScale d (j.val+3) N mu)) false = 0 := by
        have hn := higherBandRowMass_nonneg d (j.val+3) D D q a b C lam ell
          (min ell (higherBandTargetScale d (j.val+3) N mu)) false
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        change (1 ≤ min ell (higherBandTargetScale d (j.val+3) N mu)) ∧
          (false = true → ell < higherBandTargetScale d (j.val+3) N mu) ∧
          j.val+3 ≤ D ∧ 0 < higherBandRowMass d (j.val+3) D D q a b C lam ell
            (min ell (higherBandTargetScale d (j.val+3) N mu)) false
        exact ⟨hT1, (by intro h; cases h), (by have hj := j.isLt; omega), hp⟩
      have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,false))
          (higherBandFamilyGuardDegree M (j,false)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,false)) false = 0 := by
        exact higherBand_zero_mass_signed_zero d (j.val+3) D D q a b C lam ell _ hT1 false hz
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,false))
          (higherBandFamilyGuardDegree M (j,false)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,false)) false = 0 := by
        exact higherBand_coarse_below_one_signed_zero d (j.val+3) D D q a b C lam ell _ hT (not_le.mp hT1)
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
  · simp only [higherBandPhysicalIntegral, ite_true, higherBandFamilyTarget]
    by_cases hactive : ell < higherBandTargetScale d (j.val+3) N mu
    · rw [ite_eq_left hactive]
      have hT1 : 1 ≤ higherBandTargetScale d (j.val+3) N mu := hell.trans hactive.le
      have hz : higherBandRowMass d (j.val+3) M D q a b C lam ell
          (higherBandTargetScale d (j.val+3) N mu) true = 0 := by
        have hn := higherBandRowMass_nonneg d (j.val+3) M D q a b C lam ell
          (higherBandTargetScale d (j.val+3) N mu) true
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        change (1 ≤ higherBandTargetScale d (j.val+3) N mu) ∧
          (true = true → ell < higherBandTargetScale d (j.val+3) N mu) ∧
          j.val+3 ≤ M ∧ 0 < higherBandRowMass d (j.val+3) M D q a b C lam ell
            (higherBandTargetScale d (j.val+3) N mu) true
        exact ⟨hT1, fun _ => hactive, hFine j hactive, hp⟩
      have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,true))
          (higherBandFamilyGuardDegree M (j,true)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,true)) true = 0 := by
        exact higherBand_zero_mass_signed_zero d (j.val+3) M D q a b C lam ell _ hT1 true hz
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · rw [ite_eq_right hactive]

theorem higherBandFamily_signedIntegral_sum_eq_physical (d D M q : ℕ) (a b C lam ell N mu : ℝ)
    (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ) :
    (∑ i : HigherBandFamilyIndex d D M q a b C lam ell N mu,
      higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i.val) =
      ∑ i : Fin (D-2) × Bool, higherBandPhysicalIntegral d D M q a b C lam ell N mu F i := by
  classical
  exact (Finset.sum_congr_set {i | HigherBandFamilySelected d D M q a b C lam ell N mu i}
    (higherBandPhysicalIntegral d D M q a b C lam ell N mu F)
    (fun i => higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i.val)
    (fun i hi => higherBandPhysicalIntegral_selected d D M q a b C lam ell N mu F i hi)
    (fun i hi => higherBandPhysicalIntegral_unselected_zero d D M q a b C lam ell N mu hell hnu hFine F i hi)).symm

end NearlyMinimax
