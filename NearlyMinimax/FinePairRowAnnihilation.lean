module

public import NearlyMinimax.FinePairRows


@[expose] public section

/-! Every bounded Borel density observable is killed by the genuine
uncentered response packet, under its actual absolute reference law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem finite_response_density_zero {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (v : J → ℝ) (hv : ∑ j, v j = 0) (F : I → ℝ) :
    (∑ h : I × J, w h.1 * v h.2 * F h.1) = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  have he (j : J) : w i * v j * F i = (w i * F i) * v j := by ring
  simp only [he, ← Finset.mul_sum, hv, mul_zero]

section Generic
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem highPacketAbsoluteLaw_density_observable_zero (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (F : Z × HighDensityMarkIndex m r D → ℝ) (hF : Measurable F)
    (L : ℝ) (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, highPacketActivation σ a b m r D q C A e * F (e.1,e.2.1)
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 := by
  have hm : Measurable (fun e : Z × HighPacketMarkIndex ι m r D q => F (e.1,e.2.1)) :=
    hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hi := (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost).mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hbound (e.1,e.2.1)))
  rw [highPacketActivation, highPacketAbsoluteLaw, absoluteMarkLaw_activation_integral _ _
    (highPacketMarkWeight_measurable a b m r D q C A hA) hpos,
    integral_prod _ hi]
  simp only [integral_count]
  have he (ζ : Z) : (∑ h : HighPacketMarkIndex ι m r D q,
      highPacketMarkWeight a b m r D q C A (ζ,h) * F (ζ,h.1)) = 0 := by
    dsimp only [highPacketMarkWeight]
    have hz : (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C q (A ζ) h) = 0 := by
      have hr := highResponseMark_action q C (A ζ) (fun _ => 0) (fun _ => 1)
      simpa only [mul_one, responseMatrixAction_zero_mass] using hr
    exact finite_response_density_zero (densityPacketWeight a b m r D)
      (highResponseMarkWeight C q (A ζ)) hz (fun h => F (ζ,h))
  simp only [he, integral_zero]

theorem finePairPacketAbsoluteLaw_density_observable_zero (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < finePairPacketMarkMass σ a b M q C A)
    (F : Z × FinePairDensityIndex M → ℝ) (hF : Measurable F)
    (L : ℝ) (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, finePairPacketActivation σ a b M q C A e * F (e.1,e.2.1)
      ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  have hm : Measurable (fun e : Z × FinePairPacketIndex ι M q => F (e.1,e.2.1)) :=
    hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hi := (finePairPacketWeight_integrable σ a b M q C A hA hcost).mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hbound (e.1,e.2.1)))
  rw [finePairPacketActivation, finePairPacketAbsoluteLaw, absoluteMarkLaw_activation_integral _ _
    (finePairPacketWeight_measurable a b M q C A hA) hpos,
    integral_prod _ hi]
  simp only [integral_count]
  have he (ζ : Z) : (∑ h : FinePairPacketIndex ι M q,
      finePairPacketWeight a b M q C A (ζ,h) * F (ζ,h.1)) = 0 := by
    dsimp only [finePairPacketWeight]
    have hz : (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C q (A ζ) h) = 0 := by
      have hr := highResponseMark_action q C (A ζ) (fun _ => 0) (fun _ => 1)
      simpa only [mul_one, responseMatrixAction_zero_mass] using hr
    exact finite_response_density_zero (finePairDensityWeight a b M)
      (highResponseMarkWeight C q (A ζ)) hz (fun h => F (ζ,h))
  simp only [he, integral_zero]

end Generic
end NearlyMinimax
