module

public import NearlyMinimax.SourceRows
public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.HigherBandRowSource


@[expose] public section

/-! All primitive source guards for the complete singleton, pair, and
higher coarse/fine row family. Numerical guards are the only inputs. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

theorem high_source_interval_numeric {d : ℕ} (C : ModelConstants d) (M : ℝ)
    (hM : highCenterResolutionThreshold C ≤ M) :
    0 < C.densityLower+1/M ∧ C.densityLower+1/M < C.densityUpper-1/M := by
  have hg := highCenterResolution_guards C M hM
  have hM0 : 0 < M := by linarith [hg.1]
  constructor
  · linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  · linarith [hg.2,highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]

def completeSourceRows {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (Cfr lam ℓ N μ : ℝ) :=
  sourceRowData d k D M q (C.densityLower+1/(M : ℝ))
    (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ

/-- The actual singleton response/density row satisfies every source
primitive guard; its nondegeneracy and centering follow from finite rules. -/
theorem singletonRowSource_guards {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr : ℝ) (hCfr : 1 ≤ Cfr) :
    HighUnionSourceGuards C (M : ℝ) Cfr
      (singletonRowData d k D q (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr) := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hCf : 0 < Cfr := by linarith
  have hpos := singletonRowMass_positive d D q hq a b ha hab Cfr hCf
  let A := fun _ : Unit => finePairUnitMatrix d D
  have hA : ∀ i j, Measurable (fun ζ : Unit => A ζ i j) := fun _ _ => measurable_const
  have hc : Integrable (separatedMatrixCost A) (Measure.dirac ()) := by
    simp [A,separatedMatrixCost]
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => singletonRow_probability d k D q hq a b ha hab Cfr hCf
    mass_nonneg := fun _ => hpos.le
    total_positive := ?_
    activation_measurable := fun _ => absoluteActivation_measurable _ _
      (highPacketMarkWeight_measurable a b D 1 D q Cfr A hA)
    activation_bound := fun _ => highPacketActivation_bound (Measure.dirac ()) a b D 1 D q Cfr A
    activation_centered := fun _ => highPacketActivation_centered (Measure.dirac ()) a b D 1 D q Cfr A hA hc hpos
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := fun _ => highPacketIntercept_measurable a b D 1 D q
    intercept_interval := fun _ e => (densityPacketAtom_mem a b hab.le D 1 D e.2.1).1
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := fun _ _ => covarianceAtom_mem_ball Cfr hCf _ _ _ _
    time_interval := fun _ _ => responseNode_mem_unit q _ }
  · simpa [highRowTotalMass,singletonRowData,a,b] using hpos
  · intro j i
    exact (highPacketSlope_measurable a b D 1 D q (fun _ : Unit => fun _ => (1 : ℝ))
      (fun _ => measurable_const)).comp measurable_fst
  · intro j x i
    exact highPacketSlope_integrable (Measure.dirac ()) a b ha hab D 1 D q (by norm_num) Cfr A hA hc hpos
      (fun _ : Unit => fun _ => (1 : ℝ)) (fun _ => measurable_const) (by intro _ _; norm_num)
  · intro j x i
    exact highPacketAbsoluteLaw_slope_integral_zero (Measure.dirac ()) a b ha hab D 1 D q (by norm_num)
      Cfr A hA hc hpos (fun _ : Unit => fun _ => (1 : ℝ)) (fun _ => measurable_const) (by intro _ _; norm_num)
  · intro j i e x v hv
    have hh := localDensityReset_mem_interval a b ha hab 1 (by norm_num)
      (densityPacketAtom a b D 1 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 1 D e.2.1).1
      (densityPacketAtom a b D 1 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 1 D e.2.1).2
      (fun _ : Unit => v) (fun _ _ => (1 : ℝ)) () hv (by intro _; norm_num)
    convert hh using 1 <;> dsimp [singletonRowData,highPacketSlope,highPacketIntercept,localDensityReset] <;> ring
  · intro i γ
    exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 1 D q =>
      (highResponseMarkAtom Cfr q h.2).2 γ)).comp measurable_snd
  · intro i
    exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 1 D q =>
      (highResponseMarkAtom (ι := HighFrameIndex d D) 0 q h.2).1)).comp measurable_snd

/-- Restricting primitive guards to one genuine positive row preserves
all of them. The one-row total is its actual variation mass. -/
theorem HighUnionSourceGuards.restrict {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] {C : ModelConstants d} {M Cfr : ℝ}
    {R : HighUnionRowData d k F I E} (G : HighUnionSourceGuards C M Cfr R)
    (i : I) (hpos : 0 < R.rowMass i) :
    HighUnionSourceGuards C M Cfr (highUnionRowRestrict R i) where
  resolution := G.resolution
  frame := G.frame
  row_probability := fun _ => G.row_probability i
  mass_nonneg := fun _ => G.mass_nonneg i
  total_positive := by simpa [highRowTotalMass,highUnionRowRestrict] using hpos
  activation_measurable := fun _ => G.activation_measurable i
  activation_bound := fun _ => G.activation_bound i
  activation_centered := fun _ => G.activation_centered i
  slope_measurable := fun j _ => G.slope_measurable j i
  slope_integrable := fun j x _ => G.slope_integrable j x i
  slope_centered := fun j x _ => G.slope_centered j x i
  intercept_measurable := fun _ => G.intercept_measurable i
  intercept_interval := fun _ => G.intercept_interval i
  row_reset_interval := fun j _ => G.row_reset_interval j i
  vector_measurable := fun _ => G.vector_measurable i
  time_measurable := fun _ => G.time_measurable i
  vector_ball := fun _ => G.vector_ball i
  time_interval := fun _ => G.time_interval i

/-- The complete actual source family satisfies every primitive source
condition from numerical guards alone. In particular the final prior is
not restricted to the pair rows or a single higher-target packet. -/
theorem completeSourceRows_guards {d : ℕ} (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N) :
    HighUnionSourceGuards C (M : ℝ) Cfr (completeSourceRows C k D M q Cfr lam ℓ N μ) := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hCf : 0 < Cfr := by linarith
  have hcomp (i : SourceRowIndex d D M q a b Cfr lam ℓ N μ) :
      HighUnionSourceGuards C (M : ℝ) Cfr (sourceRowComponent d k D M q a b Cfr lam ℓ N μ i) := by
    cases i with
    | inl p =>
      exact (finePairSourceRows_guards C k D M q hD hq hM Cfr hCfr ℓ N hℓ hℓN).restrict p
        (finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf ℓ N hℓ hℓN p)
    | inr i =>
      cases i with
      | inl _ => exact singletonRowSource_guards C k D M q hq hM Cfr hCfr
      | inr i =>
        exact higherBandSourceRow_guards C k (higherBandFamilyTarget i.val)
          (higherBandFamilyGuardDegree M i.val) D q
          (by have hh := (higherBandFamily_target_bounds d D M q a b Cfr lam ℓ N μ i).1; omega)
          (M : ℝ) Cfr lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2 hM hCfr
          i.property.1 i.property.2.2.2
  exact {
    resolution := hM
    frame := hCfr
    row_probability := fun i => (hcomp i).row_probability ()
    mass_nonneg := fun i => (hcomp i).mass_nonneg ()
    total_positive := sourceRowTotalMass_positive d k D M q hq a b ha hab Cfr hCf lam ℓ N μ
    activation_measurable := fun i => (hcomp i).activation_measurable ()
    activation_bound := fun i => (hcomp i).activation_bound ()
    activation_centered := fun i => (hcomp i).activation_centered ()
    slope_measurable := fun j i => (hcomp i).slope_measurable j ()
    slope_integrable := fun j x i => (hcomp i).slope_integrable j x ()
    slope_centered := fun j x i => (hcomp i).slope_centered j x ()
    intercept_measurable := fun i => (hcomp i).intercept_measurable ()
    intercept_interval := fun i => (hcomp i).intercept_interval ()
    row_reset_interval := fun j i => (hcomp i).row_reset_interval j ()
    vector_measurable := fun i => (hcomp i).vector_measurable ()
    time_measurable := fun i => (hcomp i).time_measurable ()
    vector_ball := fun i => (hcomp i).vector_ball ()
    time_interval := fun i => (hcomp i).time_interval () }

end NearlyMinimax
