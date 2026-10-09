module

public import NearlyMinimax.HighReferenceBalancing
public import NearlyMinimax.PacketAbsoluteMoments


@[expose] public section

/-! The actual ordinary separated packet has a genuine centered reference
law; its slope centering follows from derivative-rule reflection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def centeredPacketLaw (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C δ : ℝ)
    (A : Z → ι → ι → ℝ) : Measure ((Z × HighPacketMarkIndex ι m r D q) ⊕ Unit) :=
  balancedReferenceLaw (highPacketAbsoluteLaw σ a b m r D q C A) δ

def centeredPacketActivation (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C δ : ℝ)
    (A : Z → ι → ι → ℝ) : (Z × HighPacketMarkIndex ι m r D q) ⊕ Unit → ℝ :=
  balancedActivation (highPacketActivation σ a b m r D q C A) δ

def centeredPacketIntercept (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C δ : ℝ)
    (A : Z → ι → ι → ℝ) : (Z × HighPacketMarkIndex ι m r D q) ⊕ Unit → ℝ :=
  balancedIntercept (highPacketIntercept a b m r D q) δ
    (∫ e, highPacketIntercept a b m r D q e ∂highPacketAbsoluteLaw σ a b m r D q C A)

def centeredPacketSlope (a b : ℝ) (m r D q : ℕ) (B : Z → Fin r → ℝ) :
    (Z × HighPacketMarkIndex ι m r D q) ⊕ Unit → ℝ :=
  balancedSlope (highPacketSlope a b m r D q B)

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (m r D q : ℕ) (C δ : ℝ)
  (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)

include hA hcost hpos

theorem centeredPacketLaw_probability (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure (centeredPacketLaw σ a b m r D q C δ A) := by
  letI := highPacketAbsoluteLaw_probability σ a b m r D q C A hA hcost hpos
  exact balancedReferenceLaw_probability _ δ hδ0 hδ1

theorem centeredPacketActivation_centered (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ e, centeredPacketActivation σ a b m r D q C δ A e
      ∂centeredPacketLaw σ a b m r D q C δ A) = 0 := by
  exact balancedActivation_integral_zero _ δ hδ hδ1 _
    (absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b m r D q C A hA))
    (absoluteActivation_integrable _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost)
      (highPacketMarkWeight_measurable a b m r D q C A hA) hpos)
    (highPacketActivation_centered σ a b m r D q C A hA hcost hpos)

theorem centeredPacketActivation_bound (hδ : 0 < δ)
    (e : (Z × HighPacketMarkIndex ι m r D q) ⊕ Unit) :
    |centeredPacketActivation σ a b m r D q C δ A e| ≤
      highPacketMarkMass σ a b m r D q C A / δ := by
  exact balancedActivation_bound _ δ _ hδ hpos.le
    (highPacketActivation_bound σ a b m r D q C A) e

theorem centeredPacketIntercept_integral_one (ha : 0 < a) (hab : a < b)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∫ e, centeredPacketIntercept σ a b m r D q C δ A e
      ∂centeredPacketLaw σ a b m r D q C δ A) = 1 :=
  balancedIntercept_integral_one _ δ hδ0 hδ1 _ (highPacketIntercept_measurable a b m r D q)
    (highPacketIntercept_integrable σ a b ha hab m r D q C A hA hcost hpos)

theorem centeredPacketSlope_integral_zero (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    (∫ e, centeredPacketSlope (ι := ι) a b m r D q B e
      ∂centeredPacketLaw σ a b m r D q C δ A) = 0 :=
  balancedSlope_integral_zero _ δ hδ0 hδ1 _ (highPacketSlope_measurable a b m r D q B hmB)
    (highPacketSlope_integrable σ a b ha hab m r D q hr C A hA hcost hpos B hmB hB)
    (highPacketAbsoluteLaw_slope_integral_zero σ a b ha hab m r D q hr C A hA hcost hpos B hmB hB)

theorem centeredPacket_expected_reset_one (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) (p : ℝ) :
    (∫ e, centeredPacketSlope a b m r D q B e * p + centeredPacketIntercept σ a b m r D q C δ A e
      ∂centeredPacketLaw σ a b m r D q C δ A) = 1 :=
  balancedReferenceLaw_expected_reset_one _ δ hδ0 hδ1 _ _
    (highPacketSlope_measurable a b m r D q B hmB) (highPacketIntercept_measurable a b m r D q)
    (highPacketSlope_integrable σ a b ha hab m r D q hr C A hA hcost hpos B hmB hB)
    (highPacketIntercept_integrable σ a b ha hab m r D q C A hA hcost hpos)
    (highPacketAbsoluteLaw_slope_integral_zero σ a b ha hab m r D q hr C A hA hcost hpos B hmB hB) p

theorem centeredPacket_signed_action (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (F : (Z × HighPacketMarkIndex ι m r D q) ⊕ Unit → ℝ) (hF : Measurable F)
    (M : ℝ) (hFM : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, centeredPacketActivation σ a b m r D q C δ A e * F e
      ∂centeredPacketLaw σ a b m r D q C δ A) =
      ∫ᵛ e, F (Sum.inl e) ∂<•highPacketSignedMeasure σ a b m r D q C A := by
  have hi := absoluteActivation_integrable _ _
    (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost)
    (highPacketMarkWeight_measurable a b m r D q C A hA) hpos
  have hiF : Integrable (fun e => highPacketActivation σ a b m r D q C A e * F (Sum.inl e))
      (highPacketAbsoluteLaw σ a b m r D q C A) := by
    exact hi.mul_bdd (hF.comp measurable_inl).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun e => hFM (Sum.inl e)))
  have hwm : Measurable (highPacketActivation σ a b m r D q C A) :=
    absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b m r D q C A hA)
  rw [centeredPacketLaw, centeredPacketActivation, balancedActivation_integral _ δ hδ hδ1
    (highPacketActivation σ a b m r D q C A) hwm F hF hiF]
  exact absoluteMarkLaw_signed_action _ _
    (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost)
    (highPacketMarkWeight_measurable a b m r D q C A hA) hpos _ (hF.comp measurable_inl) M
    (fun e => hFM (Sum.inl e))

end Packet

def highCenterResolutionThreshold {d : ℕ} (C : ModelConstants d) : ℝ :=
  max 2 (highCenterRadius C)⁻¹

theorem highCenterResolution_guards {d : ℕ} (C : ModelConstants d) (M : ℝ)
    (hM : highCenterResolutionThreshold C ≤ M) : 2 ≤ M ∧ 1 / M ≤ highCenterRadius C := by
  have hM2 : 2 ≤ M := (le_max_left _ _).trans hM
  have hMr : (highCenterRadius C)⁻¹ ≤ M := (le_max_right _ _).trans hM
  have hM0 : 0 < M := by linarith
  refine ⟨hM2, ?_⟩
  apply (div_le_iff₀ hM0).mpr
  have hh := mul_le_mul_of_nonneg_left hMr (highCenterRadius_pos C).le
  rw [mul_inv_cancel₀ (highCenterRadius_pos C).ne'] at hh
  nlinarith

end NearlyMinimax
