module

public import NearlyMinimax.HigherBandActivity


@[expose] public section

/-! The actual finite family of nonzero legal higher-target ordinary
rows. Zero signed rows are omitted, as in the manuscript. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def higherBandTargetScale (d r : ℕ) (N μ : ℝ) : ℝ :=
  N * (μ * (1 + Real.log N))^(((r : ℝ)-2)/(d : ℝ))

def higherBandFamilyTarget {D : ℕ} (i : Fin (D-2) × Bool) : ℕ := i.1.val + 3
def higherBandFamilyGuardDegree {D : ℕ} (M : ℕ) (i : Fin (D-2) × Bool) : ℕ :=
  if i.2 then M else D
def higherBandFamilyUpper (d : ℕ) {D : ℕ} (ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 then higherBandTargetScale d (higherBandFamilyTarget i) N μ
  else min ℓ (higherBandTargetScale d (higherBandFamilyTarget i) N μ)

def HigherBandFamilySelected (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : Prop :=
  1 ≤ higherBandFamilyUpper d ℓ N μ i ∧
  (i.2 = true → ℓ < higherBandTargetScale d (higherBandFamilyTarget i) N μ) ∧
  higherBandFamilyTarget i ≤ higherBandFamilyGuardDegree M i ∧
  0 < higherBandRowMass d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
    a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2

abbrev HigherBandFamilyIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  {i : Fin (D-2) × Bool // HigherBandFamilySelected d D M q a b C lam ℓ N μ i}

instance higherBandFamilyIndex_fintype (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    Fintype (HigherBandFamilyIndex d D M q a b C lam ℓ N μ) := by
  classical
  infer_instance

instance higherBandFamilyIndex_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    MeasurableSpace (HigherBandFamilyIndex d D M q a b C lam ℓ N μ) := ⊤

def HigherBandFamilyMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) : Type :=
  HigherBandRowMark d (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q i.val.2

instance higherBandFamilyMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (HigherBandFamilyMark d D M q a b C lam ℓ N μ i) := by
  dsimp [HigherBandFamilyMark]
  infer_instance

instance higherBandFamilyMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    StandardBorelSpace (HigherBandFamilyMark d D M q a b C lam ℓ N μ i) := by
  letI : StandardBorelSpace (HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2) :=
    higherBandCarrier_standardBorel _ _ _
  letI : StandardBorelSpace (HighPacketMarkIndex (HighFrameIndex d D)
      (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D q) := by infer_instance
  dsimp [HigherBandFamilyMark, higherBandFamilyMark_measurable]
  infer_instance

def higherBandFamilyComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    HighUnionRowData d k D Unit (fun _ => HigherBandFamilyMark d D M q a b C lam ℓ N μ i) :=
  higherBandRowData d k (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q
    a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2

def higherBandFamilyData (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    HighUnionRowData d k D (HigherBandFamilyIndex d D M q a b C lam ℓ N μ)
      (HigherBandFamilyMark d D M q a b C lam ℓ N μ) where
  rowLaw := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowLaw ()
  rowMass := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowMass ()
  rowActivation := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowActivation ()
  rowIntercept := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowIntercept ()
  rowSlope := fun j i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowSlope j ()
  rowVector := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowVector ()
  rowTime := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowTime ()

theorem higherBandFamily_target_bounds (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    3 ≤ higherBandFamilyTarget i.val ∧ higherBandFamilyTarget i.val ≤ D := by
  have hi := i.val.1.isLt
  dsimp [higherBandFamilyTarget]
  omega

theorem higherBandFamily_mass_positive (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    0 < (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass i := i.property.2.2.2

theorem higherBandFamily_probability (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    IsProbabilityMeasure ((higherBandFamilyData d k D M q a b C lam ℓ N μ).rowLaw i) := by
  let r := higherBandFamilyTarget i.val
  let m := higherBandFamilyGuardDegree M i.val
  let T := higherBandFamilyUpper d ℓ N μ i.val
  letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
  exact highPacketAbsoluteLaw_probability _ a b m r D q C _
    (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
    (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2) i.property.2.2.2

theorem higherBand_zero_mass_signed_zero (d r m D q : ℕ) (a b C lam L T : ℝ)
    (hT : 1 ≤ T) (fine : Bool) (hz : higherBandRowMass d r m D q a b C lam L T fine = 0) :
    higherBandSignedRow d r m D q a b C lam L T fine = 0 := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  rw [higherBandRowMass_eq_variation d r m D q a b C lam L T hT fine] at hz
  have hi := highPacketMarkWeight_integrable (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
  have hv : (higherBandSignedRow d r m D q a b C lam L T fine).variation univ ≠ ⊤ := by
    rw [higherBandSignedRow, highPacketSignedMeasure, Measure.variation_withDensityᵥ hi]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact ne_of_lt hi.hasFiniteIntegral
  have hzero : (higherBandSignedRow d r m D q a b C lam L T fine).variation univ = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right hv
  exact VectorMeasure.variation_eq_zero.mp ((Measure.measure_univ_eq_zero).mp hzero)

end NearlyMinimax
