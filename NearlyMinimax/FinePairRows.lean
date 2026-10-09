module

public import NearlyMinimax.FinePairHyperplanePacket
public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! The three genuine source fine-pair rows, on their actual finite-atom
and time/hyperplane mark spaces. The single global balancing law is applied
later by `HighUnionRowData`; these are its uncentered absolute row laws. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

inductive FinePairRowTag where
  | unit | coarse | fine
  deriving DecidableEq, Fintype

def FinePairRowMark (d D M q : ℕ) : FinePairRowTag → Type
  | .unit => Unit × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q
  | .coarse => (ℝ × FinePairFieldMark d) × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q
  | .fine => (ℝ × FinePairFieldMark d) × FinePairPacketIndex (HighFrameIndex d D) M q

instance finePairRowMark_measurable (d D M q : ℕ) (i : FinePairRowTag) :
    MeasurableSpace (FinePairRowMark d D M q i) := by
  cases i <;> dsimp [FinePairRowMark] <;> infer_instance

instance finePairRowMark_standardBorel (d D M q : ℕ) (i : FinePairRowTag) :
    StandardBorelSpace (FinePairRowMark d D M q i) := by
  letI : StandardBorelSpace (ℝ × FinePairFieldMark d) := by infer_instance
  letI : StandardBorelSpace (HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) := by infer_instance
  letI : StandardBorelSpace (FinePairPacketIndex (HighFrameIndex d D) M q) := by infer_instance
  cases i <;> dsimp [FinePairRowMark, finePairRowMark_measurable] <;> infer_instance

def finePairRowLaw (d D M q : ℕ) (a b C T₀ N : ℝ) :
    (i : FinePairRowTag) → Measure (FinePairRowMark d D M q i)
  | .unit => highPacketAbsoluteLaw (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .coarse => highPacketAbsoluteLaw (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketAbsoluteLaw (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))

def finePairRowMass (d D M q : ℕ) (a b C T₀ N : ℝ) : FinePairRowTag → ℝ
  | .unit => highPacketMarkMass (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .coarse => highPacketMarkMass (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketMarkMass (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))

def finePairRowActivation (d D M q : ℕ) (a b C T₀ N : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => highPacketActivation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .coarse => highPacketActivation (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketActivation (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))

def finePairRowIntercept (d D M q : ℕ) (a b : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => highPacketIntercept a b D 2 D q
  | .coarse => highPacketIntercept a b D 2 D q
  | .fine => finePairPacketIntercept a b M q

def finePairRowSlope (d k D M q : ℕ) (a b : ℝ) (j : HighWindowLabels d k) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → Covariate d → ℝ
  | .unit => fun e _ => highPacketSlope a b D 2 D q (fun _ _ => 1) e
  | .coarse => fun e x => highPacketSlope a b D 2 D q
      (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) e
  | .fine => fun e x => finePairPacketSlope a b M q
      (fun ζ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) e

def finePairRowVector (d D M q : ℕ) (C : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → HighFrameIndex d D → ℝ
  | .unit => fun e => (highResponseMarkAtom C q e.2.2).2
  | .coarse => fun e => (highResponseMarkAtom C q e.2.2).2
  | .fine => finePairPacketResponseVector M q C

def finePairRowTime (d D M q : ℕ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => fun e => (highResponseMarkAtom 0 q e.2.2).1
  | .coarse => fun e => (highResponseMarkAtom 0 q e.2.2).1
  | .fine => finePairPacketResponseTime M q

def finePairRowData (d k D M q : ℕ) (a b C T₀ N : ℝ) :
    HighUnionRowData d k D FinePairRowTag (FinePairRowMark d D M q) where
  rowLaw := finePairRowLaw d D M q a b C T₀ N
  rowMass := finePairRowMass d D M q a b C T₀ N
  rowActivation := finePairRowActivation d D M q a b C T₀ N
  rowIntercept := finePairRowIntercept d D M q a b
  rowSlope := finePairRowSlope d k D M q a b
  rowVector := finePairRowVector d D M q C
  rowTime := finePairRowTime d D M q

theorem finePairRowMass_nonneg (d D M q : ℕ) (a b C T₀ N : ℝ) (i : FinePairRowTag) :
    0 ≤ finePairRowMass d D M q a b C T₀ N i := by
  cases i <;> exact signedMarkMass_nonneg _ _

theorem finePairRowActivation_bound (d D M q : ℕ) (a b C T₀ N : ℝ)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    |finePairRowActivation d D M q a b C T₀ N i e| ≤ finePairRowMass d D M q a b C T₀ N i := by
  cases i <;> exact absoluteActivation_bound _ _ _

theorem finePairRowIntercept_mem (d D M q : ℕ) (a b : ℝ) (hab : a ≤ b)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    finePairRowIntercept d D M q a b i e ∈ Icc a b := by
  cases i
  · exact (densityPacketAtom_mem a b hab D 2 D e.2.1).1
  · exact (densityPacketAtom_mem a b hab D 2 D e.2.1).1
  · exact finePairPacketIntercept_mem a b hab M q e

theorem finePairRowVector_ball (d D M q : ℕ) (C : ℝ) (hC : 0 < C)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    (∑ γ, |finePairRowVector d D M q C i e γ|) ≤ C⁻¹ := by
  cases i <;> exact covarianceAtom_mem_ball C hC _ _ _ _

theorem finePairRowTime_unit (d D M q : ℕ) (i : FinePairRowTag)
    (e : FinePairRowMark d D M q i) : finePairRowTime d D M q i e ∈ Icc (0 : ℝ) 1 := by
  cases i <;> exact responseNode_mem_unit q _

theorem finePairRowSlope_bound (d k D M q : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i)
    (x : Covariate d) : |finePairRowSlope d k D M q a b j i e x| ≤ (b-a)/(4*b) := by
  cases i
  · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num)
      (fun _ : Unit => fun _ : Fin 2 => (1 : ℝ)) (by intro _ _; norm_num) e
  · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num) _
      (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le) e
  · exact finePairPacketSlope_bound a b ha hab M q _
      (fun ζ => (finePairTimeFieldValue_abs ζ _).le) e

end NearlyMinimax
