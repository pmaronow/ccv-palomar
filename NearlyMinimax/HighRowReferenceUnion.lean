module

public import NearlyMinimax.HighPacketBalancing


@[expose] public section

/-! A genuine finite tagged union of centered row references. Row selection
is weighted by its actual variation budget, preserving the source constant
and the signed generator action. Distinct zero-activation corrective tags are
allowed by the source and do not change the signed measure. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace (E j)]

theorem rowSigmaMk_measurable (j : J) : Measurable (@Sigma.mk J E j) := by
  apply Measurable.of_le_map
  exact iInf_le _ j

theorem rowSigmaFunction_measurable (F : (j : J) → E j → ℝ)
    (hF : ∀ j, Measurable (F j)) : Measurable (fun e : Sigma E => F e.1 e.2) := by
  intro s hs
  change MeasurableSet[⨅ j, MeasurableSpace.map (Sigma.mk j)
    (inferInstance : MeasurableSpace (E j))] ((fun e : Sigma E => F e.1 e.2) ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  exact fun j => hF j hs

theorem highRowReferenceUnion_standardBorel [∀ j, StandardBorelSpace (E j)] :
    StandardBorelSpace (Sigma E) := by
  letI := fun j => upgradeStandardBorel (E j)
  letI : BorelSpace (Sigma E) := historySigma_borelSpace
  infer_instance

def highRowTotalMass (B : J → ℝ) : ℝ := ∑ j, B j

theorem highRowTotalMass_pos_of_entry (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (j : J) (hj : 0 < B j) : 0 < highRowTotalMass B :=
  hj.trans_le (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ j))

def highRowSelectionProbability (B : J → ℝ) (j : J) : ℝ := B j / highRowTotalMass B

theorem highRowSelectionProbability_nonneg (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (j : J) :
    0 ≤ highRowSelectionProbability B j :=
  div_nonneg (hB j) (Finset.sum_nonneg (fun j _ => hB j))

theorem highRowSelectionProbability_pos (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (j : J) : 0 < highRowSelectionProbability B j :=
  div_pos (hB j) hTotal

theorem highRowSelectionProbability_sum (B : J → ℝ) (hTotal : highRowTotalMass B ≠ 0) :
    (∑ j, highRowSelectionProbability B j) = 1 := by
  unfold highRowSelectionProbability
  rw [← Finset.sum_div]
  exact div_self hTotal

/-- The actual positive reference law on the finite tagged mark union. -/
def highRowReferenceUnion (π : (j : J) → Measure (E j)) (B : J → ℝ) : Measure (Sigma E) :=
  ∑ j, ENNReal.ofReal (highRowSelectionProbability B j) • (π j).map (Sigma.mk j)

theorem highRowReferenceUnion_probability (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) : IsProbabilityMeasure (highRowReferenceUnion π B) := by
  constructor
  rw [highRowReferenceUnion, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.map_apply (rowSigmaMk_measurable _) MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => highRowSelectionProbability_nonneg B hB j),
    highRowSelectionProbability_sum B hTotal.ne']
  norm_num

theorem highRowReferenceUnion_integrable (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    Integrable F (highRowReferenceUnion π B) := by
  apply integrable_finsetSum_measure.mpr
  intro j _
  have h := (integrable_map_measure hF.aestronglyMeasurable (rowSigmaMk_measurable j).aemeasurable).mpr
    (hInt j)
  exact h.smul_measure ENNReal.ofReal_ne_top

theorem highRowReferenceUnion_integral (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (hB : ∀ j, 0 ≤ B j) (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    (∫ e, F e ∂highRowReferenceUnion π B) =
      ∑ j, highRowSelectionProbability B j * ∫ e, F ⟨j, e⟩ ∂π j := by
  unfold highRowReferenceUnion
  rw [integral_finsetSum_measure (fun j _ =>
    ((integrable_map_measure hF.aestronglyMeasurable (rowSigmaMk_measurable j).aemeasurable).mpr
      (hInt j)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul_measure, integral_map (rowSigmaMk_measurable j).aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal (highRowSelectionProbability_nonneg B hB j), smul_eq_mul]

def highRowUnionActivation (B : J → ℝ) (w : (j : J) → E j → ℝ) (e : Sigma E) : ℝ :=
  w e.1 e.2 / highRowSelectionProbability B e.1

theorem highRowUnionActivation_measurable (B : J → ℝ) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) : Measurable (highRowUnionActivation B w) :=
  rowSigmaFunction_measurable _ (fun j => (hw j).div_const _)

theorem highRowUnionActivation_integrable (π : (j : J) → Measure (E j))
    (B : J → ℝ) (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (hInt : ∀ j, Integrable (w j) (π j)) :
    Integrable (highRowUnionActivation B w) (highRowReferenceUnion π B) :=
  highRowReferenceUnion_integrable π B _ (highRowUnionActivation_measurable B w hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))

/-- Every row is genuinely centered; hence so is the combined activation. -/
theorem highRowUnionActivation_centered (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) (hInt : ∀ j, Integrable (w j) (π j))
    (hCenter : ∀ j, (∫ e, w j e ∂π j) = 0) :
    (∫ e, highRowUnionActivation B w e ∂highRowReferenceUnion π B) = 0 := by
  rw [highRowReferenceUnion_integral π B hB _ (highRowUnionActivation_measurable B w hw)
    (fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const (highRowSelectionProbability B j))]
  simp only [highRowUnionActivation, integral_div, hCenter, zero_div, mul_zero, Finset.sum_const_zero]

/-- The exact source activation budget is retained by the finite mixture. -/
theorem highRowUnionActivation_bound (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (δ : ℝ) (hδ : 0 < δ)
    (w : (j : J) → E j → ℝ) (hw : ∀ j e, |w j e| ≤ B j / δ) (e : Sigma E) :
    |highRowUnionActivation B w e| ≤ highRowTotalMass B / δ := by
  have hα := highRowSelectionProbability_pos B hB hTotal e.1
  unfold highRowUnionActivation
  rw [abs_div, abs_of_pos hα]
  apply (div_le_iff₀ hα).mpr
  have he : highRowTotalMass B / δ * highRowSelectionProbability B e.1 = B e.1 / δ := by
    unfold highRowSelectionProbability
    field_simp
  rw [he]
  exact hw e.1 e.2

/-- The signed action of all row tags is exactly the sum of their genuine
row actions; the mixture weights cancel and no signed action premise is used. -/
theorem highRowUnionActivation_action (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 < B j) (hTotal : 0 < highRowTotalMass B)
    (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => w j e * F ⟨j, e⟩) (π j)) :
    (∫ e, highRowUnionActivation B w e * F e ∂highRowReferenceUnion π B) =
      ∑ j, ∫ e, w j e * F ⟨j, e⟩ ∂π j := by
  have he (j : J) : (fun e : E j => highRowUnionActivation B w ⟨j,e⟩ * F ⟨j,e⟩) =
      (fun e => (w j e * F ⟨j,e⟩) / highRowSelectionProbability B j) := by
    funext e
    unfold highRowUnionActivation
    ring
  rw [highRowReferenceUnion_integral π B (fun j => (hB j).le)
    (fun e => highRowUnionActivation B w e * F e)
    ((highRowUnionActivation_measurable B w hw).mul hF)
    (fun j => by rw [he j]; exact (hInt j).div_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j, integral_div]
  exact mul_div_cancel₀ _ (highRowSelectionProbability_pos B hB hTotal j).ne'

/-- The union's true signed measure is represented by its centered positive
reference law and the bounded global activation. -/
def highRowUnionSignedMeasure (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (w : (j : J) → E j → ℝ) : SignedMeasure (Sigma E) :=
  (highRowReferenceUnion π B).withDensityᵥ (highRowUnionActivation B w)

theorem highRowUnion_signed_action (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 < B j) (hTotal : 0 < highRowTotalMass B)
    (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (hInt : ∀ j, Integrable (w j) (π j))
    (F : Sigma E → ℝ) (hF : Measurable F) (M : ℝ) (hBound : ∀ e, ‖F e‖ ≤ M) :
    (∫ᵛ e, F e ∂<•highRowUnionSignedMeasure π B w) =
      ∑ j, ∫ᵛ e, F ⟨j,e⟩ ∂<•(π j).withDensityᵥ (w j) := by
  rw [highRowUnionSignedMeasure, signedDensity_integral _ _
    (highRowUnionActivation_integrable π B w hw hInt)
    (highRowUnionActivation_measurable B w hw) F hF M hBound,
    highRowUnionActivation_action π B hB hTotal w hw F hF
      (fun j => (hInt j).mul_bdd (hF.comp (rowSigmaMk_measurable j)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun e => hBound ⟨j,e⟩)))]
  apply Finset.sum_congr rfl
  intro j _
  exact (signedDensity_integral (π j) (w j) (hInt j) (hw j) _
    (hF.comp (rowSigmaMk_measurable j)) M (fun e => hBound ⟨j,e⟩)).symm

theorem highRowReferenceUnion_integral_common_mean (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (F : (j : J) → E j → ℝ) (hF : ∀ j, Measurable (F j))
    (hInt : ∀ j, Integrable (F j) (π j)) (m : ℝ)
    (hMean : ∀ j, (∫ e, F j e ∂π j) = m) :
    (∫ e : Sigma E, F e.1 e.2 ∂highRowReferenceUnion π B) = m := by
  rw [highRowReferenceUnion_integral π B hB _ (rowSigmaFunction_measurable F hF) hInt]
  simp only [hMean]
  rw [← Finset.sum_mul, highRowSelectionProbability_sum B hTotal.ne', one_mul]

/-- The global density slope and intercept means are derived from the
already verified centered row references. -/
theorem highRowReferenceUnion_reset_means (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope intercept : (j : J) → E j → ℝ)
    (hSlope : ∀ j, Measurable (slope j)) (hIntercept : ∀ j, Measurable (intercept j))
    (hiSlope : ∀ j, Integrable (slope j) (π j))
    (hiIntercept : ∀ j, Integrable (intercept j) (π j))
    (hCenter : ∀ j, (∫ e, slope j e ∂π j) = 0)
    (hOne : ∀ j, (∫ e, intercept j e ∂π j) = 1) :
    (∫ e : Sigma E, slope e.1 e.2 ∂highRowReferenceUnion π B) = 0 ∧
      (∫ e : Sigma E, intercept e.1 e.2 ∂highRowReferenceUnion π B) = 1 :=
  ⟨highRowReferenceUnion_integral_common_mean π B hB hTotal slope hSlope hiSlope 0 hCenter,
   highRowReferenceUnion_integral_common_mean π B hB hTotal intercept hIntercept hiIntercept 1 hOne⟩

/-- Every incoming density has expected reset value one under the actual
global positive mark law. -/
theorem highRowReferenceUnion_expected_reset_one (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope intercept : (j : J) → E j → ℝ)
    (hSlope : ∀ j, Measurable (slope j)) (hIntercept : ∀ j, Measurable (intercept j))
    (hiSlope : ∀ j, Integrable (slope j) (π j))
    (hiIntercept : ∀ j, Integrable (intercept j) (π j))
    (hCenter : ∀ j, (∫ e, slope j e ∂π j) = 0)
    (hOne : ∀ j, (∫ e, intercept j e ∂π j) = 1) (p : ℝ) :
    (∫ e : Sigma E, slope e.1 e.2 * p + intercept e.1 e.2
      ∂highRowReferenceUnion π B) = 1 := by
  have hm := highRowReferenceUnion_reset_means π B hB hTotal slope intercept hSlope hIntercept
    hiSlope hiIntercept hCenter hOne
  have hiA := highRowReferenceUnion_integrable π B _
    (rowSigmaFunction_measurable slope hSlope) hiSlope
  have hiB := highRowReferenceUnion_integrable π B _
    (rowSigmaFunction_measurable intercept hIntercept) hiIntercept
  rw [integral_add (hiA.mul_const p) hiB, integral_mul_const, hm.1, hm.2, zero_mul, zero_add]

theorem highRowUnionActivation_attains_bound (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (δ : ℝ) (hδ : 0 < δ)
    (w : (j : J) → E j → ℝ) (j : J) (e : E j) (he : |w j e| = B j / δ) :
    |highRowUnionActivation B w ⟨j,e⟩| = highRowTotalMass B / δ := by
  have hα := highRowSelectionProbability_pos B hB hTotal j
  unfold highRowUnionActivation
  rw [abs_div, abs_of_pos hα, he]
  unfold highRowSelectionProbability
  field_simp [(hB j).ne']

theorem highRowUnion_reset_legal (slope intercept : (j : J) → E j → ℝ)
    (a b : ℝ)
    (hlegal : ∀ j e p, p ∈ Icc a b → slope j e * p + intercept j e ∈ Icc a b)
    (e : Sigma E) (p : ℝ) (hp : p ∈ Icc a b) :
    slope e.1 e.2 * p + intercept e.1 e.2 ∈ Icc a b := hlegal e.1 e.2 p hp

end
end NearlyMinimax
