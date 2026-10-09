module

public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.HistoryPriorDensity


@[expose] public section

/-! Actual absolute reference laws and bounded centered activation marks for
the high-smoothness signed packets. This concerns the mark law; density-reset
mean-one balancing is a separate reference-law condition. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section AbsoluteMark
variable {E : Type*} [MeasurableSpace E]

def signedMarkMass (μ : Measure E) (w : E → ℝ) : ℝ := ∫ e, |w e| ∂μ

def absoluteMarkLaw (μ : Measure E) (w : E → ℝ) : Measure E :=
  μ.withDensity (fun e => ENNReal.ofReal (|w e| / signedMarkMass μ w))

def absoluteActivation (μ : Measure E) (w : E → ℝ) (e : E) : ℝ :=
  signedMarkMass μ w * (w e / |w e|)

theorem signedMarkMass_nonneg (μ : Measure E) (w : E → ℝ) :
    0 ≤ signedMarkMass μ w := integral_nonneg (fun _ => abs_nonneg _)

theorem signedMarkMass_eq_variation (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ) :
    signedMarkMass μ w = ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable]
  simp only [signedMarkMass, Real.norm_eq_abs]

theorem absoluteMarkLaw_probability (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (hpos : 0 < signedMarkMass μ w) :
    IsProbabilityMeasure (absoluteMarkLaw μ w) := by
  constructor
  rw [absoluteMarkLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.abs.div_const _)
      (Filter.Eventually.of_forall (fun e => div_nonneg (abs_nonneg (w e)) hpos.le)),
    integral_div]
  change ENNReal.ofReal (signedMarkMass μ w / signedMarkMass μ w) = 1
  simp only [div_self hpos.ne', ENNReal.ofReal_one]

theorem absoluteActivation_measurable (μ : Measure E) (w : E → ℝ) (hw : Measurable w) :
    Measurable (absoluteActivation μ w) :=
  (hw.div hw.abs).const_mul _

theorem absoluteActivation_bound (μ : Measure E) (w : E → ℝ) (e : E) :
    |absoluteActivation μ w e| ≤ signedMarkMass μ w := by
  rw [absoluteActivation, abs_mul, abs_of_nonneg (signedMarkMass_nonneg μ w)]
  have hb : |w e / (|w e|)| ≤ 1 := by
    by_cases he : w e = 0
    · simp [he]
    · rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr he)]
  exact (mul_le_mul_of_nonneg_left hb (signedMarkMass_nonneg μ w)).trans_eq (mul_one _)

theorem absoluteActivation_integrable (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w) :
    Integrable (absoluteActivation μ w) (absoluteMarkLaw μ w) := by
  letI := absoluteMarkLaw_probability μ w hw hpos
  apply (integrable_const (signedMarkMass μ w)).mono'
    (absoluteActivation_measurable μ w hmw).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun e => by
    simpa only [Real.norm_eq_abs] using absoluteActivation_bound μ w e)

theorem absoluteMarkLaw_activation_integral (μ : Measure E) (w : E → ℝ)
    (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ e, w e * F e ∂μ := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (w e)) hpos.le), smul_eq_mul,
    absoluteActivation]
  by_cases he : w e = 0
  · simp [he]
  · field_simp

theorem absoluteActivation_centered (μ : Measure E) (w : E → ℝ)
    (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    (hzero : ∫ e, w e ∂μ = 0) :
    (∫ e, absoluteActivation μ w e ∂absoluteMarkLaw μ w) = 0 := by
  have h := absoluteMarkLaw_activation_integral μ w hmw hpos (fun _ => 1)
  simp only [mul_one] at h
  exact h.trans hzero

theorem absoluteMarkLaw_signed_action (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) =
      ∫ᵛ e, F e ∂<•(μ.withDensityᵥ w) := by
  rw [absoluteMarkLaw_activation_integral μ w hmw hpos F,
    signedDensity_integral μ w hw hmw F hF M hbound]

end AbsoluteMark

section History
variable {E J : Type*} [MeasurableSpace E] [Fintype J] [LinearOrder J]

/-- The history prior is a genuine probability law for the actual normalized
absolute signed weight. Its mark centering is proved from the signed mass. -/
theorem absoluteMark_historyPrior_probability (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    (hzero : ∫ e, w e ∂μ = 0) (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : signedMarkMass μ w ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    IsProbabilityMeasure (historyMarkedPrior dependent Δ t
      (absoluteMarkLaw μ w) (absoluteActivation μ w)) := by
  letI := absoluteMarkLaw_probability μ w hw hpos
  exact historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t B ht
    ((signedMarkMass_nonneg μ w).trans hB) (absoluteMarkLaw μ w) (absoluteActivation μ w)
    (absoluteActivation_integrable μ w hw hmw hpos)
    (absoluteActivation_centered μ w hmw hpos hzero)
    (fun e => (absoluteActivation_bound μ w e).trans hB) hsmall

end History

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def highPacketMarkMass (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × HighPacketMarkIndex ι m r D q) :=
  absoluteMarkLaw (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketActivation (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Z × HighPacketMarkIndex ι m r D q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

theorem highPacketMarkMass_eq_variation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    highPacketMarkMass σ a b m r D q C A =
      ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal :=
  signedMarkMass_eq_variation _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost)

theorem highPacketMarkWeight_integral_zero (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    (∫ e, highPacketMarkWeight a b m r D q C A e ∂σ.prod Measure.count) = 0 := by
  have h := highPacketSignedMeasure_zero_mass σ a b m r D q C A hA hcost
  rw [highPacketSignedMeasure, withDensityᵥ_apply
    (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) MeasurableSet.univ,
    Measure.restrict_univ] at h
  exact h

theorem highPacketAbsoluteLaw_probability (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    IsProbabilityMeasure (highPacketAbsoluteLaw σ a b m r D q C A) :=
  absoluteMarkLaw_probability _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) hpos

theorem highPacketActivation_centered (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    (∫ e, highPacketActivation σ a b m r D q C A e
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 :=
  absoluteActivation_centered _ _ (highPacketMarkWeight_measurable a b m r D q C A hA)
    hpos (highPacketMarkWeight_integral_zero σ a b m r D q C A hA hcost)

theorem highPacketActivation_bound (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketActivation σ a b m r D q C A e| ≤ highPacketMarkMass σ a b m r D q C A :=
  absoluteActivation_bound _ _ _

theorem highPacketActivation_exponential_bound (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketActivation σ a b m r D q C A e| ≤
      ((Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a)))) *
          (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
            ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  apply (highPacketActivation_bound σ a b m r D q C A e).trans
  rw [highPacketMarkMass_eq_variation σ a b m r D q C A hA hcost]
  exact highPacketSignedMeasure_exponential_cost σ a b ha hab m r D q hr hD C A hA hcost

end Packet
end NearlyMinimax
