module

public import NearlyMinimax.HighHistoryDensityMean
public import NearlyMinimax.HistoryReferenceMean


@[expose] public section

/-! Actual centered-packet density and mass on canonical marked histories,
including joint design measurability and the infinite reference mean. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem packetSum_borelSpace {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] : BorelSpace (A ⊕ B) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hsec := measurableSet_sum_iff.mp hs
    let : MeasurableSpace (A ⊕ B) := borel (A ⊕ B)
    let : BorelSpace (A ⊕ B) := ⟨rfl⟩
    have hleft : MeasurableSet (Sum.inl '' (Sum.inl ⁻¹' s) : Set (A ⊕ B)) :=
      Topology.IsClosedEmbedding.inl.measurableEmbedding.measurableSet_image' hsec.1
    have hright : MeasurableSet (Sum.inr '' (Sum.inr ⁻¹' s) : Set (A ⊕ B)) :=
      Topology.IsClosedEmbedding.inr.measurableEmbedding.measurableSet_image' hsec.2
    have he : s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) := by
      ext x
      cases x <;> simp
    rw [he]
    exact hleft.union hright
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr ⟨(hs.preimage continuous_inl).measurableSet,
      (hs.preimage continuous_inr).measurableSet⟩

section Canonical
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ) [NeZero k]
  [LinearOrder (HighWindowLabels d k)]
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)

def centeredPacketMarkedDensity (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighCenteredPacketMark (Z := Z) d F m r D q)) (x : Covariate d) : ℝ :=
  (historyMarkedRawState dependent (centeredPacketRawUpdate d k F m r D q σ a b C δ A B) initial h).1 x

def centeredPacketMarkedMass (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighCenteredPacketMark (Z := Z) d F m r D q)) : ℝ :=
  ∫ x, centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial h x ∂cubeVolume d

theorem centeredPacketMarkedMass_fiber (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ) (initial : HighRawState d k F)
    (g : HistoryShape (fun i j => ¬ dependent i j))
    (marks : Fin (historyShapeLength dependent g) → HighCenteredPacketMark (Z := Z) d F m r D q) :
    centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial ⟨g, marks⟩ =
      centeredPacketHistoryMass d k F m r D q σ a b C δ A B (historyShapeLength dependent g)
        (historyShapeCanonicalLabels dependent g) initial marks := rfl

theorem centeredPacketMarkedDensity_measurable (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j x l, Measurable (fun ζ => B j ζ x l)) (initial : HighRawState d k F) (x : Covariate d) :
    Measurable (fun h => centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial h x) := by
  exact (measurable_pi_apply x).comp (measurable_fst.comp
    (historyMarkedRawState_measurable dependent _
      (fun j => centeredPacketRawUpdate_measurable d k F m r D q σ a b C δ A B hB j) initial))

theorem centeredPacketMarkedDensity_joint_measurable [StandardBorelSpace Z]
    (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (initial : HighRawState d k F) (hi : Measurable initial.1) :
    Measurable (fun hx : HistoryMarked dependent
      (HighCenteredPacketMark (Z := Z) d F m r D q) × Covariate d =>
      centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial hx.1 hx.2) := by
  let E := HighCenteredPacketMark (Z := Z) d F m r D q
  letI : TopologicalSpace Z := (upgradeStandardBorel Z).toTopologicalSpace
  letI : BorelSpace Z := (upgradeStandardBorel Z).toBorelSpace
  letI : PolishSpace Z := (upgradeStandardBorel Z).toPolishSpace
  letI : TopologicalSpace (HighPacketMarkIndex (HighFrameIndex d F) m r D q) :=
    (upgradeStandardBorel (HighPacketMarkIndex (HighFrameIndex d F) m r D q)).toTopologicalSpace
  letI : BorelSpace (HighPacketMarkIndex (HighFrameIndex d F) m r D q) :=
    (upgradeStandardBorel (HighPacketMarkIndex (HighFrameIndex d F) m r D q)).toBorelSpace
  letI : PolishSpace (HighPacketMarkIndex (HighFrameIndex d F) m r D q) :=
    (upgradeStandardBorel (HighPacketMarkIndex (HighFrameIndex d F) m r D q)).toPolishSpace
  letI : BorelSpace (Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) := by infer_instance
  letI : TopologicalSpace E := inferInstance
  letI : SecondCountableTopology E := by infer_instance
  letI : BorelSpace E := packetSum_borelSpace
  letI (g : HistoryShape (fun a b => ¬ dependent a b)) :
      BorelSpace (Fin (historyShapeLength dependent g) → E) := by infer_instance
  letI : BorelSpace (HistoryMarked dependent E) := historySigma_borelSpace
  letI : BorelSpace (Σ g : HistoryShape (fun a b => ¬ dependent a b),
      (Fin (historyShapeLength dependent g) → E) × Covariate d) := historySigma_borelSpace
  let G : (Σ g : HistoryShape (fun a b => ¬ dependent a b),
      (Fin (historyShapeLength dependent g) → E) × Covariate d) → ℝ :=
    fun q' => centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial
      ⟨q'.1, q'.2.1⟩ q'.2.2
  have hG : Measurable G := by
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro g
    exact (centeredPacketRawHistory_density_joint_measurable d k F m r D q σ a b C δ A B hB
      (historyShapeLength dependent g) (historyShapeCanonicalLabels dependent g) initial hi) hs
  exact hG.comp (Homeomorph.sigmaProdDistrib
    (X := fun g : HistoryShape (fun a b => ¬ dependent a b) => Fin (historyShapeLength dependent g) → E)
    (Y := Covariate d)).continuous.measurable

theorem centeredPacketMarkedMass_measurable [StandardBorelSpace Z]
    (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (initial : HighRawState d k F) (hi : Measurable initial.1) :
    Measurable (centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial) := by
  letI := cubeVolume_isProbability d
  exact (centeredPacketMarkedDensity_joint_measurable d k F m r D q dependent σ a b C δ A B hB initial hi).stronglyMeasurable.integral_prod_right'.measurable

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1)

include hA hcost hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hB hinit

theorem centeredPacketMarkedDensity_interval
    (h : HistoryMarked dependent (HighCenteredPacketMark (Z := Z) d F m r D q)) (x : Covariate d) :
    centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial h x ∈ Icc a b :=
  centeredPacketRawHistory_density_interval d k F m r D q σ a b C δ A hA hcost hpos ha hab hr hδ0 hδ1
    radius width hR ha1 hb1 hW hδW B hB (historyShapeLength dependent h.1)
    (historyShapeCanonicalLabels dependent h.1) initial
    (fun x => by rw [hinit x]; exact ⟨by linarith, by linarith⟩) h.2 x

include hmB in
theorem centeredPacketMarkedMass_bound_and_fiber_mean :
    (∀ h, |centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial h| ≤ b) ∧
    (∀ g, (∫ marks, centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => centeredPacketLaw σ a b m r D q C δ A)) = 1) := by
  constructor
  · intro h
    exact (centeredPacketHistoryMass_bound_and_mean d k F m r D q σ a b C δ A hA hcost hpos
      ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB
      (historyShapeLength dependent h.1) (historyShapeCanonicalLabels dependent h.1) initial hinit).2.1 h.2
  · intro g
    exact (centeredPacketHistoryMass_bound_and_mean d k F m r D q σ a b C δ A hA hcost hpos
      ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB
      (historyShapeLength dependent g) (historyShapeCanonicalLabels dependent g) initial hinit).2.2

include hmB in
theorem centeredPacketMarkedDensity_reference_mean_one
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (x : Covariate d) :
    (∫ h, centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial h x
      ∂historyMarkedReference dependent Δ (centeredPacketLaw σ a b m r D q C δ A)) = 1 := by
  letI := centeredPacketLaw_probability σ a b m r D q C δ A hA hcost hpos hδ0 hδ1.le
  apply historyMarkedReference_integral_one dependent hrefl hsymm Δ hΔ hlabels _ _
    (centeredPacketMarkedDensity_measurable d k F m r D q dependent σ a b C δ A B
      (fun j x l => (hmB j l).comp (measurable_id.prodMk measurable_const)) initial x)
    (fun h => ha.le.trans (centeredPacketMarkedDensity_interval d k F m r D q dependent σ a b C δ A
      hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hB initial hinit h x).1) b
  · intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans
      (centeredPacketMarkedDensity_interval d k F m r D q dependent σ a b C δ A
        hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hB initial hinit h x).1)]
    exact (centeredPacketMarkedDensity_interval d k F m r D q dependent σ a b C δ A
      hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hB initial hinit h x).2
  · intro g
    exact centeredPacketRawHistory_canonical_density_mean_one d k F m r D q dependent σ a b C δ A
      hA hcost hpos ha hab hr hδ0 hδ1 B
      (fun j x l => (hmB j l).comp (measurable_id.prodMk measurable_const)) hB initial hinit g x

include hmB in
theorem centeredPacketMarkedMass_reference_mean_one [StandardBorelSpace Z]
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ) :
    (∫ h, centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial h
      ∂historyMarkedReference dependent Δ (centeredPacketLaw σ a b m r D q C δ A)) = 1 := by
  letI := centeredPacketLaw_probability σ a b m r D q C δ A hA hcost hpos hδ0 hδ1.le
  have hi0 : Measurable initial.1 := by
    rw [show initial.1 = (fun _ => 1) from funext hinit]
    exact measurable_const
  have hb := centeredPacketMarkedMass_bound_and_fiber_mean d k F m r D q dependent σ a b C δ A
    hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB initial hinit
  apply historyMarkedReference_integral_one dependent hrefl hsymm Δ hΔ hlabels _ _
    (centeredPacketMarkedMass_measurable d k F m r D q dependent σ a b C δ A B hmB initial hi0)
    (fun h => integral_nonneg (fun x => ha.le.trans
      (centeredPacketMarkedDensity_interval d k F m r D q dependent σ a b C δ A hA hcost hpos
        ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hB initial hinit h x).1)) b
    (fun h => by simpa only [Real.norm_eq_abs] using hb.1 h) hb.2

end Canonical
end NearlyMinimax
