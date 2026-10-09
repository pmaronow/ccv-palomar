module

public import NearlyMinimax.FinePairRowMass
public import NearlyMinimax.FinePairMatrixPositivity
public import NearlyMinimax.FinePairMatrixCost


@[expose] public section

/-! The source singleton ordinary row with its genuine one-point spatial
representation and finite density/response atoms. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev SingletonRowMark (d D q : ℕ) := Unit × HighPacketMarkIndex (HighFrameIndex d D) D 1 D q

def singletonRowMass (d D q : ℕ) (a b C : ℝ) : ℝ :=
  highPacketMarkMass (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)

def singletonRowData (d k D q : ℕ) (a b C : ℝ) :
    HighUnionRowData d k D Unit (fun _ => SingletonRowMark d D q) where
  rowLaw := fun _ => highPacketAbsoluteLaw (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
  rowMass := fun _ => singletonRowMass d D q a b C
  rowActivation := fun _ => highPacketActivation (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
  rowIntercept := fun _ => highPacketIntercept a b D 1 D q
  rowSlope := fun _ _ e _ => highPacketSlope a b D 1 D q (fun _ _ => 1) e
  rowVector := fun _ e => (highResponseMarkAtom C q e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 q e.2.2).1

theorem singletonRowMass_positive (d D q : ℕ) (hq : 1 ≤ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) (hC : 0 < C) :
    0 < singletonRowMass d D q a b C := by
  rw [singletonRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)]
  simp only [separatedMatrixCost, integral_dirac]
  rw [densityPacketWeight_variation a b ha hab D 1 D (by norm_num)]
  have hp : densityPacketPrefactor a b 1 ≠ 0 := by
    simp only [densityPacketPrefactor, Nat.factorial_one, Nat.cast_one, one_pow, one_div, inv_one, pow_one, one_mul]
    exact div_ne_zero (ha.trans hab).ne' (densityMargin_zero_ne a b ha hab)
  have hn : 0 < (derivativeOrder D : ℝ) := by
    have he : 0 < derivativeOrder D := by unfold derivativeOrder; omega
    exact_mod_cast he
  have hr : 0 < ∑ h : Fin (2*q+2), |responseWeight q h| :=
    lt_of_lt_of_le zero_lt_one (response_absolute_cost_ge_one q hq)
  have hA := finePairUnitMatrix_l1_pos d D
  exact mul_pos (mul_pos (mul_pos
    (mul_pos (mul_pos (abs_pos.mpr hp) (Real.cosh_pos _)) (pow_pos hn _)) hr)
      (mul_pos (by norm_num) (pow_pos hC _))) hA

theorem singletonRow_probability (d k D q : ℕ) (hq : 1 ≤ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) (hC : 0 < C) :
    IsProbabilityMeasure ((singletonRowData d k D q a b C).rowLaw ()) :=
  highPacketAbsoluteLaw_probability (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
    (fun _ _ => measurable_const) (integrable_const _) (singletonRowMass_positive d D q hq a b ha hab C hC)

theorem singletonRowMass_exponential_bound (d D q : ℕ) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) :
    singletonRowMass d D q a b C ≤
      (Real.exp (1+exteriorTau ((a+b)/(b-a))) * |b/densityMargin a b 0|) * D *
      Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) := by
  rw [singletonRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 1 D q C
    (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)]
  have h := highPacketSignedMeasure_exponential_cost (Measure.dirac ()) a b ha hab D 1 D q
    (by norm_num) hD C (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
  simp only [pow_one, separatedMatrixCost, integral_dirac] at h
  apply h.trans
  have hA : (∑ i, ∑ j, |finePairUnitMatrix d D i j|) ≤ 1 := finePairUnitMatrix_l1_le d D
  exact (mul_le_mul_of_nonneg_left hA (by positivity)).trans_eq (mul_one _)

end NearlyMinimax
