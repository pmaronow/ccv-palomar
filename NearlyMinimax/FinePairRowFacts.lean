module

public import NearlyMinimax.FinePairRows


@[expose] public section

/-! Primitive Borel, interval and reference-centering facts for the actual
three-row fine-pair data. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

theorem highPacketSlope_joint_measurable_finePair {Z : Type*} [MeasurableSpace Z]
    (d D q : ℕ) (a b : ℝ) (B : Z → Covariate d → Fin 2 → ℝ)
    (hB : ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)) :
    Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) × Covariate d =>
      highPacketSlope a b D 2 D q (fun ζ l => B ζ ex.2 l) ex.1) := by
  have hc : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) × Covariate d =>
      densityMargin a b (densityPacketAtom a b D 2 D ex.1.2.1).1 / (2 * b)) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      densityMargin a b (densityPacketAtom a b D 2 D h.1).1 / (2 * b))).comp
        (measurable_snd.comp measurable_fst)
  have he (l : Fin 2) : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) × Covariate d =>
      (densityPacketAtom a b D 2 D ex.1.2.1).2 l) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (densityPacketAtom a b D 2 D h.1).2 l)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (Finset.measurable_fun_sum _ (fun l _ => (he l).mul
    ((hB l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))

theorem finePairRowIntercept_measurable (d D M q : ℕ) (a b : ℝ) (i : FinePairRowTag) :
    Measurable (finePairRowIntercept d D M q a b i) := by
  cases i
  · exact highPacketIntercept_measurable a b D 2 D q
  · exact highPacketIntercept_measurable a b D 2 D q
  · exact finePairPacketIntercept_measurable a b M q

theorem finePairRowVector_measurable (d D M q : ℕ) (C : ℝ) (i : FinePairRowTag)
    (γ : HighFrameIndex d D) : Measurable (fun e => finePairRowVector d D M q C i e γ) := by
  cases i
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom C q h.2).2 γ)).comp measurable_snd
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom C q h.2).2 γ)).comp measurable_snd
  · exact (measurable_of_countable (fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
      (highResponseMarkAtom C q h.2).2 γ)).comp measurable_snd

theorem finePairRowTime_measurable (d D M q : ℕ) (i : FinePairRowTag) :
    Measurable (finePairRowTime d D M q i) := by
  cases i
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom 0 q h.2).1)).comp measurable_snd
  · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom 0 q h.2).1)).comp measurable_snd
  · exact (measurable_of_countable (fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
      (highResponseMarkAtom 0 q h.2).1)).comp measurable_snd

theorem finePairRowSlope_joint_measurable (d k D M q : ℕ) (a b : ℝ)
    (j : HighWindowLabels d k) (i : FinePairRowTag) :
    Measurable (fun ex : FinePairRowMark d D M q i × Covariate d =>
      finePairRowSlope d k D M q a b j i ex.1 ex.2) := by
  have hψ : Measurable (fun zx : (ℝ × FinePairFieldMark d) × Covariate d =>
      finePairTimeFieldValue zx.1 (highLocalCoordinates d k j zx.2)) :=
    (finePairTimeFieldValue_measurable d).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  cases i
  · exact (highPacketSlope_measurable a b D 2 D q (fun _ : Unit => fun _ => (1 : ℝ))
      (fun _ => measurable_const)).comp measurable_fst
  · exact highPacketSlope_joint_measurable_finePair d D q a b
      (fun ζ x _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) (fun _ => hψ)
  · exact finePairPacketSlope_joint_measurable a b M q
      (fun ζ x => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hψ

theorem finePairRow_reset_interval (d k D M q : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i)
    (x : Covariate d) (v : ℝ) (hv : v ∈ Icc a b) :
    finePairRowSlope d k D M q a b j i e x * v + finePairRowIntercept d D M q a b i e ∈ Icc a b := by
  cases i
  · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
      (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
      (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).2
      (fun _ : Unit => v) (fun _ _ => 1) () hv (by intro _; norm_num)
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
      (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
      (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).2
      (fun _ : Unit => v) (fun _ _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x))
      () hv (fun _ => (finePairTimeFieldValue_abs e.1 _).le)
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := finePairDensityReset_mem_interval a b ha hab _ _
      (finePairPacketIntercept_mem a b hab.le M q e) (fineModulationNode_bound e.2.1.2)
      (fun _ : Unit => v) (fun _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x)) () hv
      (finePairTimeFieldValue_abs e.1 _).le
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, finePairPacketSlope,
      finePairPacketIntercept, finePairDensityReset, finePairDensityAtom] <;> ring

section Reference
variable (d : ℕ) [NeZero d] (k D M q : ℕ) (a b C T₀ N : ℝ)
    (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
include hpos

theorem finePairRowLaw_probability (i : FinePairRowTag) :
    IsProbabilityMeasure (finePairRowLaw d D M q a b C T₀ N i) := by
  cases i
  · exact highPacketAbsoluteLaw_probability (Measure.dirac ()) a b D 2 D q C (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
  · exact highPacketAbsoluteLaw_probability (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
  · exact finePairPacketAbsoluteLaw_probability (finePairTimeFieldMeasure d T₀ N) a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)

theorem finePairRowActivation_measurable (i : FinePairRowTag) :
    Measurable (finePairRowActivation d D M q a b C T₀ N i) := by
  cases i
  · exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b D 2 D q C _
      (fun _ _ => measurable_const))
  · exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b D 2 D q C _
      (finePairTimeMatrix_measurable d _))
  · exact absoluteActivation_measurable _ _ (finePairPacketWeight_measurable a b M q C _
      (finePairTimeMatrix_measurable d _))

theorem finePairRowActivation_centered (i : FinePairRowTag) :
    (∫ e, finePairRowActivation d D M q a b C T₀ N i e ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  cases i
  · exact highPacketActivation_centered (Measure.dirac ()) a b D 2 D q C (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
  · exact highPacketActivation_centered (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
  · exact finePairPacketActivation_centered (finePairTimeFieldMeasure d T₀ N) a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)

theorem finePairRowSlope_integrable (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (x : Covariate d) (i : FinePairRowTag) :
    Integrable (fun e => finePairRowSlope d k D M q a b j i e x)
      (finePairRowLaw d D M q a b C T₀ N i) := by
  letI := finePairRowLaw_probability d D M q a b C T₀ N hpos i
  have hm : Measurable (fun e : FinePairRowMark d D M q i => finePairRowSlope d k D M q a b j i e x) :=
    (finePairRowSlope_joint_measurable d k D M q a b j i).comp
    (measurable_id.prodMk (measurable_const (a := x)))
  apply (integrable_const ((b-a)/(4*b))).mono' hm.aestronglyMeasurable
  filter_upwards [] with e
  simpa only [Real.norm_eq_abs] using finePairRowSlope_bound d k D M q a b ha hab j i e x

theorem finePairRowSlope_centered (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (x : Covariate d) (i : FinePairRowTag) :
    (∫ e, finePairRowSlope d k D M q a b j i e x ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  have hm : Measurable (fun ζ : ℝ × FinePairFieldMark d =>
      finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) :=
    (boundedHyperplaneFieldValue_section_measurable d _).comp measurable_snd
  cases i
  · exact highPacketAbsoluteLaw_slope_integral_zero (Measure.dirac ()) a b ha hab D 2 D q (by norm_num)
      C (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
      (fun _ : Unit => fun _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)
  · exact highPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d 0 T₀) a b ha hab
      D 2 D q (by norm_num) C _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
      (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) (fun _ => hm)
      (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le)
  · exact finePairPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d T₀ N) a b M q
      C _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)
      ha hab (fun ζ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hm
      (fun ζ => (finePairTimeFieldValue_abs ζ _).le)

end Reference
end NearlyMinimax
