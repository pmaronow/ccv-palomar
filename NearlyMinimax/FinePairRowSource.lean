module

public import NearlyMinimax.FinePairRowNondegenerate
public import NearlyMinimax.HighUnionSource


@[expose] public section

/-! Concrete source guards for all three actual fine-pair rows. No row-law,
mean-zero, positive variation or reset legality premise is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

def finePairSourceRows {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (Cfr T₀ N : ℝ) :
    HighUnionRowData d k D FinePairRowTag (FinePairRowMark d D M q) :=
  finePairRowData d k D M q (C.densityLower+1/(M : ℝ))
    (C.densityUpper-1/(M : ℝ)) Cfr T₀ N

/-- The three true unit/coarse/fine packet rows satisfy every primitive
source guard under their physical numerical parameter conditions. -/
theorem finePairSourceRows_guards {d : ℕ} (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr : ℝ) (hCfr : 1 ≤ Cfr) (T₀ N : ℝ) (hT₀ : 0 < T₀) (hTN : T₀ < N) :
    HighUnionSourceGuards C (M : ℝ) Cfr (finePairSourceRows C k D M q Cfr T₀ N) := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  have hg := highCenterResolution_guards C (M : ℝ) hM
  have hM0 : (0 : ℝ) < M := by linarith [hg.1]
  have hr := highCenterRadius_pos C
  have hmargin := highCenterRadius_le_margins C
  have ha : 0 < a := by dsimp [a]; linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hab : a < b := by dsimp [a,b]; linarith [hg.2]
  have hCf : 0 < Cfr := by linarith
  have hpos := finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf T₀ N hT₀ hTN
  refine {
    resolution := hM
    frame := hCfr
    row_probability := ?_
    mass_nonneg := ?_
    total_positive := ?_
    activation_measurable := ?_
    activation_bound := ?_
    activation_centered := ?_
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := ?_
    intercept_interval := ?_
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := ?_
    time_interval := ?_ }
  · exact finePairRowLaw_probability d D M q a b Cfr T₀ N hpos
  · exact finePairRowMass_nonneg d D M q a b Cfr T₀ N
  · exact Finset.sum_pos' (fun i _ => (hpos i).le) ⟨.unit, Finset.mem_univ _, hpos .unit⟩
  · exact finePairRowActivation_measurable d D M q a b Cfr T₀ N hpos
  · exact finePairRowActivation_bound d D M q a b Cfr T₀ N
  · exact finePairRowActivation_centered d D M q a b Cfr T₀ N hpos
  · exact finePairRowSlope_joint_measurable d k D M q a b
  · exact finePairRowSlope_integrable d k D M q a b Cfr T₀ N hpos ha hab
  · exact finePairRowSlope_centered d k D M q a b Cfr T₀ N hpos ha hab
  · exact finePairRowIntercept_measurable d D M q a b
  · exact finePairRowIntercept_mem d D M q a b hab.le
  · exact finePairRow_reset_interval d k D M q a b ha hab
  · exact finePairRowVector_measurable d D M q Cfr
  · exact finePairRowTime_measurable d D M q
  · exact finePairRowVector_ball d D M q Cfr hCf
  · exact finePairRowTime_unit d D M q

end NearlyMinimax
