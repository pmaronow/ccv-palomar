module

public import NearlyMinimax.FinePairDensityPacket


@[expose] public section

/-! The actual fine-pair density packet tensored with the original finite
response reset measure, retaining the genuine field and scale marks. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

abbrev FinePairPacketIndex (ι : Type*) (M q : ℕ) := FinePairDensityIndex M × HighResponseMarkIndex ι q

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def finePairPacketWeight (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  finePairDensityWeight a b M e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2

theorem finePairPacketWeight_slice_measurable (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (h : FinePairPacketIndex ι M q) : Measurable (fun ζ => finePairPacketWeight a b M q C A (ζ, h)) := by
  dsimp [finePairPacketWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop

theorem finePairPacketWeight_measurable (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) :
    Measurable (finePairPacketWeight a b M q C A) :=
  measurable_from_prod_countable_left (finePairPacketWeight_slice_measurable a b M q C A hA)

theorem finePairPacketWeight_slice_integrable (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (h : FinePairPacketIndex ι M q) :
    Integrable (fun ζ => finePairPacketWeight a b M q C A (ζ, h)) σ := by
  dsimp [finePairPacketWeight, highResponseMarkWeight, covarianceWeight]
  exact (((((separatedMatrix_entry_integrable σ A hA hcost h.2.1.1 h.2.1.2).const_mul
    (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul
      (responseWeight q h.2.2.2)).const_mul (finePairDensityWeight a b M h.1)

theorem finePairPacketWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    Integrable (finePairPacketWeight a b M q C A) (σ.prod Measure.count) :=
  joint_finite_integrable σ _ (finePairPacketWeight_slice_measurable a b M q C A hA)
    (finePairPacketWeight_slice_integrable σ a b M q C A hA hcost)

def finePairPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × FinePairPacketIndex ι M q) :=
  (σ.prod Measure.count).withDensityᵥ (finePairPacketWeight a b M q C A)

theorem finePairPacketSignedMeasure_integral (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (f : Z × FinePairPacketIndex ι M q → ℝ) (hf : ∀ h, Measurable (fun ζ => f (ζ, h)))
    (L : ℝ) (hb : ∀ ζ h, ‖f (ζ, h)‖ ≤ L) :
    (∫ᵛ e, f e ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∫ ζ, ∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h) * f (ζ, h) ∂σ := by
  have hm := measurable_from_prod_countable_left hf
  have hw := finePairPacketWeight_integrable σ a b M q C A hA hcost
  rw [finePairPacketSignedMeasure, signedDensity_integral _ _ hw
    (finePairPacketWeight_measurable a b M q C A hA) f hm L (fun e => hb e.1 e.2),
    integral_prod _ (hw.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun e => hb e.1 e.2)))]
  simp only [integral_count]

theorem finePairPacketWeight_variation (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, |finePairPacketWeight a b M q C A (ζ, h)|) =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) * separatedMatrixCost A ζ := by
  rw [Fintype.sum_prod_type]
  simp only [finePairPacketWeight, abs_mul]
  simp_rw [← Finset.mul_sum, highResponseMark_variation]
  rw [← Finset.sum_mul]
  unfold separatedMatrixCost
  ring

theorem finePairPacketSignedMeasure_totalVariation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((finePairPacketSignedMeasure σ a b M q C A).variation univ).toReal =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
          (∫ ζ, separatedMatrixCost A ζ ∂σ) := by
  have hw := finePairPacketWeight_integrable σ a b M q C A hA hcost
  rw [finePairPacketSignedMeasure, Measure.variation_withDensityᵥ hw,
    withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable, integral_prod _ hw.norm]
  simp only [integral_count, Real.norm_eq_abs, finePairPacketWeight_variation]
  rw [integral_const_mul]

def finePairPacketObservable (a b : ℝ) (M q : ℕ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  G e.1 (finePairDensityAtom a b M e.2.1).1 (finePairDensityAtom a b M e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)

theorem finePairPacketObservable_finite_action (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h) *
      finePairPacketObservable a b M q C c G Φ (ζ, h)) =
      (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ := by
  rw [Fintype.sum_prod_type, finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairPacketWeight, finePairPacketObservable]
  have he (h : FinePairDensityIndex M) (v : HighResponseMarkIndex ι q) :
      finePairDensityWeight a b M h * highResponseMarkWeight C q (A ζ) v *
      (G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2 *
        Φ (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1)) =
      (finePairDensityWeight a b M h * G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2) *
        (highResponseMarkWeight C q (A ζ) v *
          Φ (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1)) := by ring
  simp_rw [he, ← Finset.mul_sum, highResponseMark_action]
  rw [← Finset.sum_mul]

theorem finePairPacketSignedMeasure_factor_integral (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (hG : ∀ z eps, Measurable (fun ζ => G ζ z eps))
    (L : ℝ) (hL : 0 ≤ L) (hGbound : ∀ ζ h,
      |G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2| ≤ L)
    (Φ : (ι → ℝ) → ℝ) (R : ℝ) (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b M q C c G Φ e ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∫ ζ, (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  rw [finePairPacketSignedMeasure_integral σ a b M q C A hA hcost _
    (fun h => by
      change Measurable (fun ζ => G ζ (finePairDensityAtom a b M h.1).1
        (finePairDensityAtom a b M h.1).2 *
        Φ (coefficientReset c (highResponseMarkAtom C q h.2).2 (highResponseMarkAtom C q h.2).1))
      exact (hG _ _).mul_const _) (L * R) (fun ζ h => by
      rw [finePairPacketObservable, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGbound ζ h.1) (hΦ h.2) (abs_nonneg _) hL)]
  simp_rw [finePairPacketObservable_finite_action]

theorem finePairPacketSignedMeasure_conditional_zero_mass (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (hG : ∀ z eps, Measurable (fun ζ => G ζ z eps))
    (L : ℝ) (hL : 0 ≤ L) (hGbound : ∀ ζ h,
      |G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2| ≤ L) :
    (∫ᵛ e, finePairPacketObservable a b M q C c G (fun _ => 1) e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) = 0 := by
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c G hG L hL hGbound
    (fun _ => 1) 1 (by intro h; norm_num)]
  simp_rw [responseMatrixAction_zero_mass, mul_zero]
  exact integral_zero _ _

theorem finePairPacketSignedMeasure_conditional_zero_mean (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (hG : ∀ z eps, Measurable (fun ζ => G ζ z eps))
    (L : ℝ) (hL : 0 ≤ L) (hGbound : ∀ ζ h,
      |G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2| ≤ L) (i : ι) :
    (∫ᵛ e, finePairPacketObservable a b M q C c G (fun v => v i) e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) = 0 := by
  let R := ∑ h : HighResponseMarkIndex ι q,
    |coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1 i|
  have hΦ (h : HighResponseMarkIndex ι q) :
      |coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1 i| ≤ R := by
    dsimp [R]
    exact Finset.single_le_sum (fun v _ => abs_nonneg
      (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1 i)) (Finset.mem_univ h)
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c G hG L hL hGbound
    (fun v => v i) R hΦ]
  simp_rw [responseMatrixAction_zero_mean, mul_zero]
  exact integral_zero _ _

theorem finePairPacketSignedMeasure_pair_action {U : Type*} (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (M q : ℕ) (hM : 2 ≤ M) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1)
    (u v : U) (Φ : (ι → ℝ) → ℝ) (R : ℝ) (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u *
        finePairDensityReset a b z eps p (ψ ζ) v) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      p u * p v * (∫ ζ, ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  have hm (z eps : ℝ) (u : U) :
      Measurable (fun ζ => finePairDensityReset a b z eps p (ψ ζ) u) := by
    unfold finePairDensityReset
    exact measurable_const.add ((hmψ u).const_mul _)
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c
    (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u * finePairDensityReset a b z eps p (ψ ζ) v)
    (fun z eps => (hm z eps u).mul (hm z eps v)) (b ^ 2) (by positivity) (fun ζ h => by
      rw [abs_mul, pow_two]
      exact mul_le_mul (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ (ζ, h) u)
        (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ (ζ, h) v) (abs_nonneg _) (ha.trans hab).le) Φ R hΦ]
  simp_rw [finePairDensitySignedRule_pair_exact a b ha hab M hM p]
  have he (ζ : Z) : p u * p v * ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ =
      (p u * p v) * (ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [he]
  exact integral_const_mul _ _

end Packet
end NearlyMinimax
