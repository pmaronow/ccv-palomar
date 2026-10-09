module

public import NearlyMinimax.HighSeparatedRows
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod


@[expose] public section

/-! The actual joint signed measure of density, separated-representation,
and response marks used by the high-smoothness local update. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section SignedDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Integration against an actual real weighted signed measure, for a
bounded measurable observable. The signed-density integral identity is
derived from its positive and negative parts. -/
theorem signedDensity_integral (w : X → ℝ) (hw : Integrable w μ) (hmw : Measurable w)
    (f : X → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ x, ‖f x‖ ≤ M) :
    (∫ᵛ x, f x ∂<•(μ.withDensityᵥ w)) = ∫ x, w x * f x ∂μ := by
  let μp := μ.withDensity (fun x => ENNReal.ofReal (w x))
  let μn := μ.withDensity (fun x => ENNReal.ofReal (-w x))
  letI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  letI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hw.neg.hasFiniteIntegral
  have hp : Integrable f μp := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hn : Integrable f μn := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hpv : μp.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hp
  have hnv : μn.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hn
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hw,
    VectorMeasure.integral_sub_vectorMeasure hpv hnv, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  dsimp only [μp, μn]
  have hmn : Measurable (fun x => ENNReal.ofReal (-w x)) := hmw.neg.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmw.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hmn
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hpf := hw.pos_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hnf := hw.neg_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [← integral_sub hpf hnf]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have he : max (w x) 0 - max (-w x) 0 = w x := by
    by_cases hh : 0 ≤ w x <;> simp [max_eq_left, max_eq_right, hh, neg_nonpos.mpr, neg_nonneg.mpr]
  dsimp only
  rw [← sub_mul, he]

end SignedDensity

section FiniteProduct
variable {Z I : Type*} [MeasurableSpace Z] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

theorem finite_count_integrable (f : I → ℝ) : Integrable f Measure.count := by
  have hm : Measurable f := measurable_of_countable f
  apply (integrable_const (∑ i, ‖f i‖)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun i =>
    Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i))

theorem joint_finite_integrable (σ : Measure Z) [IsFiniteMeasure σ] (f : Z × I → ℝ)
    (hf : ∀ i, Measurable (fun ζ => f (ζ, i)))
    (hi : ∀ i, Integrable (fun ζ => f (ζ, i)) σ) :
    Integrable f (σ.prod Measure.count) := by
  have hm : Measurable f := measurable_from_prod_countable_left hf
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun ζ => finite_count_integrable _), ?_⟩
  simp only [integral_count]
  exact integrable_finsetSum _ (fun i _ => (hi i).norm)

end FiniteProduct

abbrev HighDensityMarkIndex (m r D : ℕ) :=
  Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))

abbrev HighResponseMarkIndex (ι : Type*) (q : ℕ) := (ι × ι) × (Bool × Bool) × Fin (2 * q + 2)

abbrev HighPacketMarkIndex (ι : Type*) (m r D q : ℕ) :=
  HighDensityMarkIndex m r D × HighResponseMarkIndex ι q

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def highResponseMarkAtom (C : ℝ) (q : ℕ) (h : HighResponseMarkIndex ι q) :
    ℝ × (ι → ℝ) :=
  (responseNode q h.2.2, covarianceAtom C h.1.1 h.1.2 h.2.1.1 h.2.1.2)

def highResponseMarkWeight (C : ℝ) (q : ℕ) (A : ι → ι → ℝ)
    (h : HighResponseMarkIndex ι q) : ℝ :=
  responseWeight q h.2.2 * covarianceWeight C A h.1.1 h.1.2 h.2.1.1 h.2.1.2

def highPacketMarkWeight (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  densityPacketWeight a b m r D e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2

theorem highPacketMarkWeight_slice_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (h : HighPacketMarkIndex ι m r D q) :
    Measurable (fun ζ => highPacketMarkWeight a b m r D q C A (ζ, h)) := by
  dsimp [highPacketMarkWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop

theorem highPacketMarkWeight_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) :
    Measurable (highPacketMarkWeight a b m r D q C A) :=
  measurable_from_prod_countable_left (highPacketMarkWeight_slice_measurable a b m r D q C A hA)

theorem highPacketMarkWeight_slice_integrable (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (h : HighPacketMarkIndex ι m r D q) :
    Integrable (fun ζ => highPacketMarkWeight a b m r D q C A (ζ, h)) σ := by
  dsimp [highPacketMarkWeight, highResponseMarkWeight, covarianceWeight]
  exact (((((separatedMatrix_entry_integrable σ A hA hcost h.2.1.1 h.2.1.2).const_mul
    (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul
      (responseWeight q h.2.2.2)).const_mul (densityPacketWeight a b m r D h.1)

theorem highPacketMarkWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    Integrable (highPacketMarkWeight a b m r D q C A) (σ.prod Measure.count) :=
  joint_finite_integrable σ _ (highPacketMarkWeight_slice_measurable a b m r D q C A hA)
    (highPacketMarkWeight_slice_integrable σ a b m r D q C A hA hcost)

/-- The original joint Xi packet as a genuine signed measure, represented
on the finite atom indices together with the actual positive sigma mark. -/
def highPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × HighPacketMarkIndex ι m r D q) :=
  (σ.prod Measure.count).withDensityᵥ (highPacketMarkWeight a b m r D q C A)

theorem highPacketSignedMeasure_integral (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (F : Z × HighPacketMarkIndex ι m r D q → ℝ)
    (hF : ∀ h, Measurable (fun ζ => F (ζ, h))) (M : ℝ)
    (hBound : ∀ ζ h, ‖F (ζ, h)‖ ≤ M) :
    (∫ᵛ e, F e ∂<•(highPacketSignedMeasure σ a b m r D q C A)) =
      ∫ ζ, ∑ h : HighPacketMarkIndex ι m r D q,
        highPacketMarkWeight a b m r D q C A (ζ, h) * F (ζ, h) ∂σ := by
  have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
  have hmF : Measurable F := measurable_from_prod_countable_left hF
  have hb : ∀ e : Z × HighPacketMarkIndex ι m r D q, ‖F e‖ ≤ M := fun e => hBound e.1 e.2
  rw [highPacketSignedMeasure, signedDensity_integral _ _ hw
    (highPacketMarkWeight_measurable a b m r D q C A hA) F hmF M hb,
    integral_prod _ (hw.mul_bdd hmF.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
  simp only [integral_count]

theorem highResponseMark_action (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C q A h *
      Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)) =
      responseMatrixAction q C A c Φ := by
  simp only [Fintype.sum_prod_type, highResponseMarkWeight, highResponseMarkAtom,
    responseMatrixAction, covarianceAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro h _
  ring

def highPacketObservable (a b : ℝ) (m r D q : ℕ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  G e.1 (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom a b m r D e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)

theorem highPacketObservable_finite_action (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : HighPacketMarkIndex ι m r D q,
      highPacketMarkWeight a b m r D q C A (ζ, h) * highPacketObservable a b m r D q C c G Φ (ζ, h)) =
      densityPacketAction a b m r D (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) := by
  rw [Fintype.sum_prod_type]
  have he (h : HighDensityMarkIndex m r D) :
      (∑ v : HighResponseMarkIndex ι q,
        highPacketMarkWeight a b m r D q C A (ζ, (h, v)) *
          highPacketObservable a b m r D q C c G Φ (ζ, (h, v))) =
      densityPacketWeight a b m r D h *
        (G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2 *
          responseMatrixAction q C (A ζ) c Φ) := by
    rw [← highResponseMark_action q C (A ζ) c Φ]
    simp only [Finset.mul_sum, highPacketMarkWeight, highPacketObservable]
    apply Finset.sum_congr rfl
    intro v _
    ring
  simp_rw [he]
  have hi := densityPacketSignedRule_integral a b m r D
    (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ)
  rw [densityPacketSignedRule, atomicSignedRule_integral] at hi
  exact hi

/-- The joint signed integral equals the actual iterated Xi action used
in the local-row theorem. -/
theorem highPacketSignedMeasure_factor_integral (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (L : ℝ) (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L)
    (Φ : (ι → ℝ) → ℝ) (M : ℝ)
    (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ M) :
    (∫ᵛ e, highPacketObservable a b m r D q C c G Φ e
      ∂<•(highPacketSignedMeasure σ a b m r D q C A)) =
      highSeparatedPacketAction σ a b m r D q C A c G Φ := by
  have hmF (h : HighPacketMarkIndex ι m r D q) :
      Measurable (fun ζ => highPacketObservable a b m r D q C c G Φ (ζ, h)) := by
    change Measurable (fun ζ => G ζ (densityPacketAtom a b m r D h.1).1
      (densityPacketAtom a b m r D h.1).2 *
        Φ (coefficientReset c (highResponseMarkAtom C q h.2).2 (highResponseMarkAtom C q h.2).1))
    exact (hG _ _).mul_const _
  rw [highPacketSignedMeasure_integral σ a b m r D q C A hA hcost _
    hmF (L * M)]
  · simp only [highPacketObservable_finite_action, highSeparatedPacketAction]
  · intro ζ h
    rw [highPacketObservable, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGbound ζ h.1) (hΦ h.2) (abs_nonneg _) hL

theorem highPacketSignedMeasure_variation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal =
      ∫ ζ, ∑ h : HighPacketMarkIndex ι m r D q,
        |highPacketMarkWeight a b m r D q C A (ζ, h)| ∂σ := by
  have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
  rw [highPacketSignedMeasure, Measure.variation_withDensityᵥ hw,
    withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable,
    integral_prod _ hw.norm]
  simp only [integral_count, Real.norm_eq_abs]

theorem highResponseMark_variation (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, |highResponseMarkWeight C q A h|) =
      (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) := by
  simp only [highResponseMarkWeight, Fintype.sum_prod_type, abs_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [covariance_weight_variation]

theorem highPacketMarkWeight_variation (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (ζ : Z) :
    (∑ h : HighPacketMarkIndex ι m r D q, |highPacketMarkWeight a b m r D q C A (ζ, h)|) =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) * separatedMatrixCost A ζ := by
  rw [Fintype.sum_prod_type]
  simp only [highPacketMarkWeight, abs_mul]
  simp_rw [← Finset.mul_sum, highResponseMark_variation]
  rw [← Finset.sum_mul]
  unfold separatedMatrixCost
  ring

/-- Exact raw-atom variation of Xi: the density packet cost, fixed scalar
response cost and signed covariance cost multiply the actual representation cost. -/
theorem highPacketSignedMeasure_totalVariation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
          ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  rw [highPacketSignedMeasure_variation σ a b m r D q C A hA hcost]
  simp only [highPacketMarkWeight_variation]
  rw [integral_const_mul]

theorem densityPacketAtom_injective (a b : ℝ) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) : Function.Injective (densityPacketAtom a b m r D) := by
  intro e f he
  apply Prod.ext
  · exact (exteriorNode_strictAnti a b hab (m + r) (by omega)).injective (congrArg Prod.fst he)
  · funext l
    exact (lobattoNode_strictAnti (derivativeOrder D) (by unfold derivativeOrder; omega)).injective
      (congrArg (fun e : ℝ × (Fin r → ℝ) => e.2 l) he)

theorem densityPacketWeight_exponential_cost (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) ≤
      (Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have he := atomicSignedRule_totalVariation_eq (densityPacketAtom a b m r D)
    (densityPacketWeight a b m r D) (densityPacketAtom_injective a b hab m r D hr)
  rw [← he]
  exact densityPacketSignedRule_exponential_cost a b ha hab m r D hr hD

theorem highPacketSignedMeasure_exponential_cost (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal ≤
      ((Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a)))) *
          (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
            ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  rw [highPacketSignedMeasure_totalVariation σ a b m r D q C A hA hcost]
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (densityPacketWeight_exponential_cost a b ha hab m r D hr hD)
        (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    · positivity
  · apply integral_nonneg
    intro ζ
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg (A ζ i j)))

theorem highPacketSignedMeasure_zero_mass (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    highPacketSignedMeasure σ a b m r D q C A univ = 0 := by
  have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
  rw [highPacketSignedMeasure, withDensityᵥ_apply hw MeasurableSet.univ, Measure.restrict_univ,
    integral_prod _ hw]
  simp only [integral_count]
  have hz (ζ : Z) : (∑ h : HighPacketMarkIndex ι m r D q,
      highPacketMarkWeight a b m r D q C A (ζ, h)) = 0 := by
    have h := highPacketObservable_finite_action a b m r D q C A (fun _ => 0)
      (fun _ _ _ => 1) (fun _ => 1) ζ
    simpa only [highPacketObservable, mul_one, mul_zero, responseMatrixAction_zero_mass,
      densityPacketAction_zero] using h
  simp only [hz, integral_zero]

theorem highPacketSignedMeasure_conditional_zero_mass (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (L : ℝ) (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L) :
    (∫ᵛ e, highPacketObservable a b m r D q C c G (fun _ => 1) e
      ∂<•(highPacketSignedMeasure σ a b m r D q C A)) = 0 := by
  rw [highPacketSignedMeasure_factor_integral σ a b m r D q C A hA hcost c G hG L hL hGbound
    (fun _ => 1) 1 (by intro h; norm_num), highSeparatedPacketAction_annihilates_constants]

theorem highPacketSignedMeasure_conditional_zero_mean (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (L : ℝ) (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L) (i : ι) :
    (∫ᵛ e, highPacketObservable a b m r D q C c G (fun v => v i) e
      ∂<•(highPacketSignedMeasure σ a b m r D q C A)) = 0 := by
  let M := ∑ h : HighResponseMarkIndex ι q,
    |coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1 i|
  have hΦ (h : HighResponseMarkIndex ι q) :
      |coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1 i| ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun v _ =>
      abs_nonneg (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1 i))
        (Finset.mem_univ h)
  rw [highPacketSignedMeasure_factor_integral σ a b m r D q C A hA hcost c G hG L hL hGbound
    (fun v => v i) M hΦ, highSeparatedPacketAction_annihilates_coordinates]

variable {α : Type*} [DecidableEq α]

/-- Original LB-loc-row as an integral against the actual joint signed
measure Xi. Node bounds and every Fubini integrability condition are
derived from legal resets and the primitive finite representation cost. -/
theorem highPacketSignedMeasure_local_row (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D) (p : α → ℝ) (hp : ∀ i ∈ S, p i ∈ Icc a b)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (hC : 0 < C)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ) (hc : ∑ i, |c i| ≤ C⁻¹)
    (Φ : (ι → ℝ) → ℝ) (M : ℝ) (hΦ : ∀ v, (∑ i, |v i|) ≤ C⁻¹ → |Φ v| ≤ M) :
    (∫ᵛ e, highPacketObservable a b m r D q C c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ e
      ∂<•(highPacketSignedMeasure σ a b m r D q C A)) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ := by
  have hmG (z : ℝ) (ε : Fin r → ℝ) :
      Measurable (fun ζ => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) := by
    apply Finset.measurable_fun_prod
    intro i _
    unfold localDensityReset
    exact ((Finset.measurable_fun_sum _ (fun l _ => (hB i l).const_mul (ε l))).const_mul
      (densityMargin a b z / ((r : ℝ) * b) * p i)).const_add z
  have hbG (ζ : Z) (h : HighDensityMarkIndex m r D) :
      |∏ i ∈ S, localDensityReset a b r (densityPacketAtom a b m r D h).1
        (densityPacketAtom a b m r D h).2 p (B ζ) i| ≤ b ^ S.card := by
    have hn := densityPacketAtom_mem a b hab.le m r D h
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i ∈ S, b := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro i hi
        have hl := localDensityReset_mem_interval a b ha hab r hr _ hn.1 _ hn.2 p (B ζ) i
          (hp i hi) (hBbound ζ i)
        rw [abs_of_nonneg (ha.le.trans hl.1)]
        exact hl.2
      _ = _ := Finset.prod_const _
  have hΦnodes (h : HighResponseMarkIndex ι q) :
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ M := by
    apply hΦ
    exact coefficientReset_mem_ball C c _ _ (responseNode_mem_unit q h.2.2) hc
      (covarianceAtom_mem_ball C hC h.1.1 h.1.2 h.2.1.1 h.2.1.2)
  rw [highPacketSignedMeasure_factor_integral σ a b m r D q C A hA hcost c _ hmG
    (b ^ S.card) (pow_nonneg (ha.trans hab).le _) hbG Φ M hΦnodes]
  exact highSeparatedPacketAction_row σ a b ha hab m r D q hr hD S hSD p B hB hBbound C A hA hcost c Φ

end Packet

/-- The selected coefficient is also exactly the paper's point-permutation
average, as opposed to the equivalent mark-assignment enumeration. -/
theorem densitySeparatedSym_eq_point_permutation_average {α : Type*} [DecidableEq α]
    (r : ℕ) (B : α → Fin r → ℝ) (S : Finset α) (e : Fin r ≃ S) :
    densitySeparatedSym r B S =
      (∑ σ : Equiv.Perm (Fin r), ∏ l, B (e (σ l)) l) / (r.factorial : ℝ) := by
  classical
  rw [densitySeparatedSym_eq_permutation_average r B S e]
  apply congrArg (fun x : ℝ => x / (r.factorial : ℝ))
  let symmEquiv : Equiv.Perm (Equiv.Perm (Fin r)) :=
    ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
  apply Fintype.sum_equiv symmEquiv
  intro σ
  change (∏ i, B (e i) (σ i)) = (∏ l, B (e (σ.symm l)) l)
  have h := σ.symm.prod_comp (fun i => B (e i) (σ i))
  simpa only [Equiv.apply_symm_apply] using h.symm

end NearlyMinimax
