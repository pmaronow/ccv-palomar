module

public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.HistoryInvariantLaw
public import NearlyMinimax.HistoryPatchStateAppend
public import NearlyMinimax.HighMassAnnihilation


@[expose] public section

/-!
# The actual balanced-packet invariant mass law

The source dependency relation is the genuine torus-neighbor relation.
-/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem highCenteredPacketMark_standardBorelSpace {Z : Type*} [MeasurableSpace Z]
    [StandardBorelSpace Z] (d F m r D q : ℕ) :
    StandardBorelSpace (HighCenteredPacketMark (Z := Z) d F m r D q) := by
  letI : TopologicalSpace Z := (upgradeStandardBorel Z).toTopologicalSpace
  letI : BorelSpace Z := (upgradeStandardBorel Z).toBorelSpace
  letI : PolishSpace Z := (upgradeStandardBorel Z).toPolishSpace
  letI : TopologicalSpace (HighPacketMarkIndex (HighFrameIndex d F) m r D q) :=
    (upgradeStandardBorel (HighPacketMarkIndex (HighFrameIndex d F) m r D q)).toTopologicalSpace
  letI : BorelSpace (HighPacketMarkIndex (HighFrameIndex d F) m r D q) :=
    (upgradeStandardBorel (HighPacketMarkIndex (HighFrameIndex d F) m r D q)).toBorelSpace
  letI : PolishSpace (HighPacketMarkIndex (HighFrameIndex d F) m r D q) :=
    (upgradeStandardBorel (HighPacketMarkIndex (HighFrameIndex d F) m r D q)).toPolishSpace
  letI : BorelSpace (HighCenteredPacketMark (Z := Z) d F m r D q) := packetSum_borelSpace
  infer_instance

theorem highNeighbor_dependency_card (d k : ℕ) [NeZero k] (j : HighWindowLabels d k) :
    (dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j).card ≤ 3^d := by
  classical
  have he : dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j =
      highNeighborLabels d k j := by
    ext i
    simp [dependentLabelFinset]
  rw [he]
  exact highNeighborLabels_card_le d k j

/-- The true tilted exceptional mass probability is determined by the genuine mass law. -/
theorem massPowerTilt_abs_event_eq_of_massLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (m : Ω → ℝ) (hm : Measurable m) (n : ℕ)
    (hlaw : μ.map m = ν.map m) (ε : ℝ) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} =
      (massPowerTilt ν m n).real {ω | ε < |m ω - 1|} := by
  have hS : MeasurableSet {z : ℝ | ε < |z - 1|} :=
    measurableSet_lt measurable_const ((measurable_id.sub measurable_const).abs)
  have he := congrArg (fun μ' : Measure ℝ => μ' {z : ℝ | ε < |z - 1|})
    (massPowerTilt_massLaw_eq μ ν m hm n hlaw)
  rw [Measure.map_apply hm hS, Measure.map_apply hm hS] at he
  exact congrArg ENNReal.toReal he

section ActualMassLaw
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (initial : HighRawState d k F) (hi : Measurable initial.1)
  (T : ℝ) (hT : 0 ≤ T)
  (hsmall : T * (highPacketMarkMass σ a b m r D q C A / δ) / historyReferenceRho (3^d) ≤
    1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2))

include hA hcost hpos hδ hδ1 hmB hi hT hsmall

/-- The actual positive source prior has the invariant true raw mass law.
The local indicator cancellation follows from the constructed full packet. -/
theorem centeredPacketMarkedMass_prior_law (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
      σ a b C δ A B initial)
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (centeredPacketLaw σ a b m r D q C δ A) (centeredPacketActivation σ a b m r D q C δ A)) =
    Measure.map (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
      σ a b C δ A B initial)
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (centeredPacketLaw σ a b m r D q C δ A)) := by
  let := centeredPacketLaw_probability σ a b m r D q C δ A hA hcost hpos hδ.le hδ1
  let := highCenteredPacketMark_standardBorelSpace (Z := Z) d F m r D q
  have ham : Measurable (centeredPacketActivation σ a b m r D q C δ A) :=
    balancedActivation_measurable _
      (absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b m r D q C A hA)) δ
  exact historyMarkedPrior_invariant_law (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (3^d) (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    T (highPacketMarkMass σ a b m r D q C A / δ) hT (div_nonneg hpos.le hδ.le)
    (centeredPacketLaw σ a b m r D q C δ A) (centeredPacketActivation σ a b m r D q C δ A) ham
    (centeredPacketActivation_centered σ a b m r D q C δ A hA hcost hpos hδ hδ1)
    (centeredPacketActivation_bound σ a b m r D q C δ A hA hcost hpos hδ) hsmall
    _ (centeredPacketMarkedMass_measurable d k F m r D q
      (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A B hmB initial hi)
    (centeredPacketMarkedMass_append_indicator_zero d k F m r D q σ a b C δ A
      hA hcost hpos hδ hδ1 B hmB initial hi) t ht

/-- Genuine centered packet marks and the source numerical guard produce a probability path. -/
theorem centeredPacketMarkedPrior_probability (t : ℝ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
      (centeredPacketLaw σ a b m r D q C δ A) (centeredPacketActivation σ a b m r D q C δ A)) := by
  let := centeredPacketLaw_probability σ a b m r D q C δ A hA hcost hpos hδ.le hδ1
  have ham : Measurable (centeredPacketActivation σ a b m r D q C δ A) :=
    balancedActivation_measurable _
      (absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b m r D q C A hA)) δ
  have hbound := centeredPacketActivation_bound σ a b m r D q C δ A hA hcost hpos hδ
  have hBp : 0 ≤ highPacketMarkMass σ a b m r D q C A / δ := div_nonneg hpos.le hδ.le
  have hai : Integrable (centeredPacketActivation σ a b m r D q C δ A)
      (centeredPacketLaw σ a b m r D q C δ A) :=
    Integrable.of_bound ham.aestronglyMeasurable (highPacketMarkMass σ a b m r D q C A / δ)
      (Filter.Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using hbound e)
  have hs : t * (highPacketMarkMass σ a b m r D q C A / δ) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBp)
      (historyReferenceRho_pos (3^d)).le).trans hsmall
  exact historyMarkedPrior_probability (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (3^d) (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    t _ ht.1 hBp _ _ hai
    (centeredPacketActivation_centered σ a b m r D q C δ A hA hcost hpos hδ hδ1) hbound hs

/-- The genuine mass-power normalizer is constant along the constructed source path. -/
theorem centeredPacketMarkedMass_normalizer_constant (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    massPowerNormalizer
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (centeredPacketLaw σ a b m r D q C δ A) (centeredPacketActivation σ a b m r D q C δ A))
      (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
        σ a b C δ A B initial) n =
    massPowerNormalizer
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (centeredPacketLaw σ a b m r D q C δ A))
      (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
        σ a b C δ A B initial) n :=
  massPowerNormalizer_eq_of_massLaw _ _ _
    (centeredPacketMarkedMass_measurable d k F m r D q
      (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A B hmB initial hi) n
    (centeredPacketMarkedMass_prior_law d k F m r D q σ a b C δ A hA hcost hpos hδ hδ1
      B hmB initial hi T hT hsmall t ht)

variable (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδlt : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1) (hinit : ∀ x, initial.1 x = 1)

include ha hab hr hδlt hR ha1 hb1 hW hδW hB hinit

/-- The actual mass-power tilted positive history prior is a probability measure at every source time. -/
theorem centeredPacketMarkedMass_tiltedPrior_probability (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (centeredPacketLaw σ a b m r D q C δ A) (centeredPacketActivation σ a b m r D q C δ A))
      (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
        σ a b C δ A B initial) n) := by
  let := centeredPacketMarkedPrior_probability d k F m r D q σ a b C δ A hA hcost hpos hδ hδ1
    B hmB initial hi T hT hsmall t ht
  exact massPowerTilt_isProbability _ _
    (centeredPacketMarkedMass_measurable d k F m r D q
      (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A B hmB initial hi)
    n a b ha
    (fun h => centeredPacketMarkedMass_interval d k F m r D q
      (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A hA hcost hpos ha hab hr hδ.le hδlt
      radius width hR ha1 hb1 hW hδW B hmB hB initial hinit h)

/-- The source exceptional mass tail holds for the actual constructed tilted prior at every source time. -/
theorem centeredPacketMarkedMass_prior_tilted_tail (hk : 2 ≤ k) (n : ℕ) (ε : ℝ)
    (hε : 8 * highHistoryMassParameter d k a b * (n : ℝ) ≤ ε) (t : ℝ) (ht : t ∈ Icc 0 T) :
    (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (centeredPacketLaw σ a b m r D q C δ A) (centeredPacketActivation σ a b m r D q C δ A))
      (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
        σ a b C δ A B initial) n).real
      {h | ε < |centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
        σ a b C δ A B initial h - 1|} ≤
      2 * Real.exp (-ε^2 / (8 * highHistoryMassParameter d k a b)) := by
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _
    (centeredPacketMarkedMass_measurable d k F m r D q
      (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A B hmB initial hi) n
    (centeredPacketMarkedMass_prior_law d k F m r D q σ a b C δ A hA hcost hpos hδ hδ1
      B hmB initial hi T hT hsmall t ht) ε]
  exact centeredPacketMarkedMass_tilted_tail d k F m r D q
    (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A hA hcost hpos ha hab hr hδ.le hδlt
    radius width hR ha1 hb1 hW hδW B hmB hB initial hinit hk
    (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (3^d) (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k) n ε hε

end ActualMassLaw

end NearlyMinimax
