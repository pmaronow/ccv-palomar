module

public import NearlyMinimax.HigherBandRows
public import NearlyMinimax.HighUnionSource
public import NearlyMinimax.FinePairRowAnnihilation


@[expose] public section

/-! Original source primitive legality for each actual higher-target
cardinal/cardinal-band row. The selected family supplies positive actual
variation; all law, centering, Borel, and reset facts are derived. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

theorem highPacketSlope_joint_measurable_general {Z : Type*} [MeasurableSpace Z]
    (d m r D q : ℕ) (a b : ℝ) (B : Z → Covariate d → Fin r → ℝ)
    (hB : ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)) :
    Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      highPacketSlope a b m r D q (fun ζ l => B ζ ex.2 l) ex.1) := by
  have hc : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      densityMargin a b (densityPacketAtom a b m r D ex.1.2.1).1 / ((r : ℝ)*b)) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      densityMargin a b (densityPacketAtom a b m r D h.1).1 / ((r : ℝ)*b))).comp
        (measurable_snd.comp measurable_fst)
  have he (l : Fin r) : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      (densityPacketAtom a b m r D ex.1.2.1).2 l) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      (densityPacketAtom a b m r D h.1).2 l)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (Finset.measurable_fun_sum _ (fun l _ => (he l).mul
    ((hB l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))

def higherBandSourceRow {d : ℕ} (C : ModelConstants d) (k r m D q : ℕ)
    (M Cfr lam L T : ℝ) (fine : Bool) :
    HighUnionRowData d k D Unit (fun _ => HigherBandRowMark d r m D q fine) :=
  higherBandRowData d k r m D q (C.densityLower+1/M) (C.densityUpper-1/M) Cfr lam L T fine

/-- Every actual selected positive-mass higher-band row satisfies the
source's primitive probability, reset, and mean-one balancing inputs. -/
theorem higherBandSourceRow_guards {d : ℕ} (C : ModelConstants d)
    (k r m D q : ℕ) (hr : 1 ≤ r) (M Cfr lam L T : ℝ) (fine : Bool)
    (hM : highCenterResolutionThreshold C ≤ M) (hCfr : 1 ≤ Cfr) (hT : 1 ≤ T)
    (hpos : 0 < higherBandRowMass d r m D q (C.densityLower+1/M)
      (C.densityUpper-1/M) Cfr lam L T fine) :
    HighUnionSourceGuards C M Cfr (higherBandSourceRow C k r m D q M Cfr lam L T fine) := by
  let a := C.densityLower+1/M
  let b := C.densityUpper-1/M
  let σ := higherBandCarrierMeasure d r L T fine
  let A := higherBandCarrierAmplitude d r D lam fine
  let B := fun (j : HighWindowLabels d k) ζ (x : Covariate d) l =>
    higherBandCarrierFactor d r lam fine ζ l (highLocalCoordinates d k j x)
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  have hA := higherBandCarrierAmplitude_measurable d r D lam fine
  have hc := higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine
  have hg := highCenterResolution_guards C M hM
  have hM0 : 0 < M := by linarith [hg.1]
  have ha : 0 < a := by dsimp [a]; linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  have hab : a < b := by
    dsimp [a,b]
    linarith [hg.2,highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]
  have hCf : 0 < Cfr := by linarith
  have hB (j) (l : Fin r) : Measurable (fun ζx : HigherBandCarrier d r fine × Covariate d =>
      B j ζx.1 ζx.2 l) :=
    (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  have hBb (j) (ζ : HigherBandCarrier d r fine) (x : Covariate d) (l : Fin r) : |B j ζ x l| ≤ 1 :=
    higherBandCarrierFactor_bound d r lam fine ζ l _ (fun i =>
      (highLocalCoordinates_abs_le_one d k j x i).trans (by norm_num))
  have hBm (j) (x : Covariate d) (l : Fin r) : Measurable (fun ζ => B j ζ x l) :=
    (hB j l).comp (measurable_id.prodMk measurable_const)
  have hp := highPacketAbsoluteLaw_probability σ a b m r D q Cfr A hA hc hpos
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => hp
    mass_nonneg := fun _ => hpos.le
    total_positive := ?_
    activation_measurable := ?_
    activation_bound := fun _ => higherBandRowActivation_bound d r m D q a b Cfr lam L T fine
    activation_centered := fun _ => highPacketActivation_centered σ a b m r D q Cfr A hA hc hpos
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := fun _ => highPacketIntercept_measurable a b m r D q
    intercept_interval := ?_
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := ?_
    time_interval := ?_ }
  · simpa [highRowTotalMass,higherBandSourceRow,higherBandRowData] using hpos
  · intro i
    exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b m r D q Cfr A hA)
  · intro j i
    exact highPacketSlope_joint_measurable_general d m r D q a b (fun ζ x l => B j ζ x l) (hB j)
  · intro j x i
    exact highPacketSlope_integrable σ a b ha hab m r D q hr Cfr A hA hc hpos
      (fun ζ l => B j ζ x l) (hBm j x) (fun ζ l => hBb j ζ x l)
  · intro j x i
    exact highPacketAbsoluteLaw_slope_integral_zero σ a b ha hab m r D q hr Cfr A hA hc hpos
      (fun ζ l => B j ζ x l) (hBm j x) (fun ζ l => hBb j ζ x l)
  · intro i e
    exact (densityPacketAtom_mem a b hab.le m r D e.2.1).1
  · intro j i e x v hv
    have hh := localDensityReset_mem_interval a b ha hab r hr
      (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom_mem a b hab.le m r D e.2.1).1
      (densityPacketAtom a b m r D e.2.1).2 (densityPacketAtom_mem a b hab.le m r D e.2.1).2
      (fun _ : Unit => v) (fun _ l => B j e.1 x l) () hv (fun l => hBb j e.1 x l)
    convert hh using 1 <;>
      dsimp [higherBandSourceRow,higherBandRowData,highPacketSlope,highPacketIntercept,localDensityReset] <;> ring
  · intro i γ
    exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      (highResponseMarkAtom Cfr q h.2).2 γ)).comp measurable_snd
  · intro i
    exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      (highResponseMarkAtom (ι := HighFrameIndex d D) 0 q h.2).1)).comp measurable_snd
  · intro i e
    exact covarianceAtom_mem_ball Cfr hCf _ _ _ _
  · intro i e
    exact responseNode_mem_unit q _


/-- The actual higher-band response atoms kill every bounded Borel
observable of the retained carrier and density atom index. -/
theorem higherBandRow_density_observable_zero (d r m D q : ℕ)
    (a b Cfr lam L T : ℝ) (fine : Bool) (hT : 1 ≤ T)
    (hpos : 0 < higherBandRowMass d r m D q a b Cfr lam L T fine)
    (H : HigherBandCarrier d r fine × HighDensityMarkIndex m r D → ℝ)
    (hH : Measurable H) (B : ℝ) (hB : ∀ z, ‖H z‖ ≤ B) :
    (∫ e, higherBandRowActivation d r m D q a b Cfr lam L T fine e * H (e.1,e.2.1)
      ∂higherBandRowLaw d r m D q a b Cfr lam L T fine) = 0 := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  exact highPacketAbsoluteLaw_density_observable_zero _ a b m r D q Cfr _
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
    hpos H hH B hB

end NearlyMinimax
