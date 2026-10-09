module

public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HistoryMassConcentration
public import NearlyMinimax.MassTiltTail


@[expose] public section

/-!
# Concentration of the actual balanced-packet history mass

The packet's full representation mark is retained. The finite recursion,
actual torus patch geometry, and independent label blocks prove the infinite
reference MGF. The true mass-power tilt then has the exceptional tail bound.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The exact bounded-differences coefficient for the actual torus labels. -/
def highHistoryMassParameter (d k : ℕ) (a b : ℝ) : ℝ :=
  (k : ℝ)^d * ((2 / (k : ℝ))^d * (b-a))^2 / 8

theorem highHistoryMassParameter_pos (d k : ℕ) (a b : ℝ) (hk : 0 < k) (hab : a < b) :
    0 < highHistoryMassParameter d k a b := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold highHistoryMassParameter
  positivity

/-- The exact parameter has the paper's inverse-grid-cardinality dependence. -/
theorem highHistoryMassParameter_eq (d k : ℕ) (a b : ℝ) (hk : 0 < k) :
    highHistoryMassParameter d k a b = (2 : ℝ)^(2*d) * (b-a)^2 / (8 * (k : ℝ)^d) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : (k : ℝ)^d ≠ 0 := ne_of_gt (pow_pos hkR d)
  unfold highHistoryMassParameter
  rw [div_pow, mul_pow, Nat.mul_comm 2 d, pow_mul]
  field_simp

section ActualPacket
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1)

include hA hcost hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hmB hB hinit

theorem centeredPacketMarkedMass_interval
    (h : HistoryMarked dependent (HighCenteredPacketMark (Z := Z) d F m r D q)) :
    centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial h ∈ Icc a b := by
  let := cubeVolume_isProbability d
  have hi : Measurable initial.1 := by
    rw [show initial.1 = (fun _ => 1) from funext hinit]
    exact measurable_const
  have hp : Measurable (fun x => centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial h x) :=
    (centeredPacketMarkedDensity_joint_measurable d k F m r D q dependent σ a b C δ A B hmB initial hi).comp
      (measurable_const.prodMk measurable_id)
  have hb := centeredPacketMarkedDensity_interval d k F m r D q dependent σ a b C δ A
    hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hB initial hinit h
  have hpI : Integrable (fun x => centeredPacketMarkedDensity d k F m r D q dependent σ a b C δ A B initial h x)
      (cubeVolume d) := Integrable.of_bound hp.aestronglyMeasurable b (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (ha.trans_le (hb x).1)]
    exact (hb x).2)
  constructor
  · have hh := integral_mono (integrable_const a) hpI (fun x => (hb x).1)
    simpa only [centeredPacketMarkedMass, integral_const, probReal_univ, one_smul] using hh
  · have hh := integral_mono hpI (integrable_const b) (fun x => (hb x).2)
    simpa only [centeredPacketMarkedMass, integral_const, probReal_univ, one_smul] using hh

omit [StandardBorelSpace Z] in
/-- Replacing an entire actual label block changes raw mass by at most patch volume times interval width. -/
theorem centeredPacketMarkedMass_block_oscillation (hk : 2 ≤ k)
    (g : HistoryShape (fun i j => ¬ dependent i j))
    (marks marks' : Fin (historyShapeLength dependent g) → HighCenteredPacketMark (Z := Z) d F m r D q)
    (j : HighWindowLabels d k)
    (hm : ∀ i, historyShapeCanonicalLabels dependent g i ≠ j → marks i = marks' i) :
    |centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial ⟨g, marks⟩ -
      centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial ⟨g, marks'⟩| ≤
      (2 / (k : ℝ))^d * (b-a) := by
  have hi : Measurable initial.1 := by
    rw [show initial.1 = (fun _ => 1) from funext hinit]
    exact measurable_const
  exact highAffineMarkedMass_block_oscillation d k hk dependent
    (fun j e x => centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e)
    (fun _ e _ => centeredPacketIntercept σ a b m r D q C δ A e)
    (fun j e => (centeredPacketSlope_joint_measurable d F m r D q a b (B j) (hmB j)).comp
      (measurable_const.prodMk measurable_id))
    (fun _ _ => measurable_const)
    (fun _ => centeredPacketResponseReset d F m r D q C)
    a b hab.le
    (fun j e x v hv => centeredPacket_reset_interval d F m r D q σ a b C δ A hA hcost hpos
      ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW (fun ζ l => B j ζ x l) (fun ζ l => hB j ζ x l) e v hv)
    initial hi (fun x => by rw [hinit x]; exact ⟨by linarith, by linarith⟩) g marks marks' j hm

/-- The actual infinite canonical reference has the source mass MGF, derived from packet balancing and geometry. -/
theorem centeredPacketMarkedMass_reference_mgf (hk : 2 ≤ k)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ) (u : ℝ) :
    (∫ h, Real.exp (u * (centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial h - 1))
      ∂historyMarkedReference dependent Δ (centeredPacketLaw σ a b m r D q C δ A)) ≤
      Real.exp (highHistoryMassParameter d k a b * u^2) := by
  let := centeredPacketLaw_probability σ a b m r D q C δ A hA hcost hpos hδ0 hδ1.le
  have hi : Measurable initial.1 := by
    rw [show initial.1 = (fun _ => 1) from funext hinit]
    exact measurable_const
  have hb := centeredPacketMarkedMass_bound_and_fiber_mean d k F m r D q dependent σ a b C δ A
    hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB initial hinit
  have hh := historyMarkedReference_mass_mgf dependent hrefl hsymm Δ hΔ hlabels
    (centeredPacketLaw σ a b m r D q C δ A)
    (centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial)
    (centeredPacketMarkedMass_measurable d k F m r D q dependent σ a b C δ A B hmB initial hi)
    b ((2 / (k : ℝ))^d * (b-a)) (by positivity) hb.1 hb.2
    (fun g j marks marks' hm => centeredPacketMarkedMass_block_oscillation d k F m r D q dependent
      σ a b C δ A hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB initial hinit
      hk g marks marks' j hm) u
  have hc : Fintype.card (HighWindowLabels d k) = k^d := by
    simp [HighWindowLabels, ZMod.card]
  rw [hc, Nat.cast_pow] at hh
  convert hh using 1
  congr 1
  unfold highHistoryMassParameter
  ring

/-- The actual reference tilted by the sample mass power has the genuine exceptional tail.
Only packet, reset, geometry, and the explicit numerical epsilon guard are hypotheses. -/
theorem centeredPacketMarkedMass_tilted_tail (hk : 2 ≤ k)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (n : ℕ) (ε : ℝ) (hε : 8 * highHistoryMassParameter d k a b * (n : ℝ) ≤ ε) :
    (massPowerTilt (historyMarkedReference dependent Δ (centeredPacketLaw σ a b m r D q C δ A))
      (centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial) n).real
      {h | ε < |centeredPacketMarkedMass d k F m r D q dependent σ a b C δ A B initial h - 1|} ≤
      2 * Real.exp (-ε^2 / (8 * highHistoryMassParameter d k a b)) := by
  let := centeredPacketLaw_probability σ a b m r D q C δ A hA hcost hpos hδ0 hδ1.le
  let := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels
    (centeredPacketLaw σ a b m r D q C δ A)
  have hi : Measurable initial.1 := by
    rw [show initial.1 = (fun _ => 1) from funext hinit]
    exact measurable_const
  exact massPowerTilt_abs_tail _ _
    (centeredPacketMarkedMass_measurable d k F m r D q dependent σ a b C δ A B hmB initial hi)
    n a b ha
    (fun h => centeredPacketMarkedMass_interval d k F m r D q dependent σ a b C δ A
      hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB initial hinit h)
    (centeredPacketMarkedMass_reference_mean_one d k F m r D q dependent σ a b C δ A
      hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB initial hinit
      hrefl hsymm Δ hΔ hlabels)
    (highHistoryMassParameter d k a b) ε (highHistoryMassParameter_pos d k a b (by omega) hab)
    (fun u => centeredPacketMarkedMass_reference_mgf d k F m r D q dependent σ a b C δ A
      hA hcost hpos ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hmB hB initial hinit
      hk hrefl hsymm Δ hΔ hlabels u) hε

end ActualPacket
end NearlyMinimax
