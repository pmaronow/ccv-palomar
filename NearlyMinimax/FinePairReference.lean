module

public import NearlyMinimax.FinePairResponsePacket
public import NearlyMinimax.HighReferenceBalancing


@[expose] public section

/-! The genuine uncentered absolute fine-pair reference law. Reflection of
the actual three-point modulation atoms centers its affine density slope. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem fineModulationNode_reflection (i : Fin 3) : fineModulationNode i.rev = -fineModulationNode i := by
  fin_cases i <;> norm_num [fineModulationNode, Fin.rev]

theorem fineModulationWeight_abs_reflection (i : Fin 3) :
    |fineModulationWeight i.rev| = |fineModulationWeight i| := by
  fin_cases i <;> norm_num [fineModulationWeight, Fin.rev]

def finePairPacketReflection (ι : Type*) (M q : ℕ) : Equiv.Perm (FinePairPacketIndex ι M q) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) Fin.revPerm) (Equiv.refl _)

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def finePairPacketMarkMass (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × FinePairPacketIndex ι M q) :=
  absoluteMarkLaw (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketActivation (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Z × FinePairPacketIndex ι M q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketIntercept (a b : ℝ) (M q : ℕ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  (finePairDensityAtom a b M e.2.1).1

def finePairPacketSlope (a b : ℝ) (M q : ℕ) (ψ : Z → ℝ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  densityMargin a b (finePairPacketIntercept a b M q e) / b *
    (finePairDensityAtom a b M e.2.1).2 * ψ e.1

def finePairPacketResponseVector (M q : ℕ) (C : ℝ) (e : Z × FinePairPacketIndex ι M q) : ι → ℝ :=
  (highResponseMarkAtom C q e.2.2).2

def finePairPacketResponseTime (M q : ℕ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  (highResponseMarkAtom 0 q e.2.2).1

theorem finePairPacketResponseVector_mem_ball (M q : ℕ) (C : ℝ) (hC : 0 < C)
    (e : Z × FinePairPacketIndex ι M q) : (∑ i, |finePairPacketResponseVector M q C e i|) ≤ C⁻¹ :=
  covarianceAtom_mem_ball C hC _ _ _ _

theorem finePairPacketResponseTime_mem_unit (M q : ℕ) (e : Z × FinePairPacketIndex ι M q) :
    finePairPacketResponseTime M q e ∈ Icc (0 : ℝ) 1 :=
  responseNode_mem_unit q _

theorem finePairPacketIntercept_measurable (a b : ℝ) (M q : ℕ) :
    Measurable (finePairPacketIntercept (Z := Z) (ι := ι) a b M q) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun _ : Z => (finePairDensityAtom a b M h.1).1)
  exact measurable_const

theorem finePairPacketSlope_measurable (a b : ℝ) (M q : ℕ) (ψ : Z → ℝ) (hψ : Measurable ψ) :
    Measurable (finePairPacketSlope (ι := ι) a b M q ψ) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold finePairPacketSlope finePairPacketIntercept
  dsimp only
  exact hψ.const_mul _

theorem finePairPacketSlope_joint_measurable {U : Type*} [MeasurableSpace U]
    (a b : ℝ) (M q : ℕ) (ψ : Z → U → ℝ)
    (hψ : Measurable (fun zu : Z × U => ψ zu.1 zu.2)) :
    Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      finePairPacketSlope a b M q (fun ζ => ψ ζ eu.2) eu.1) := by
  have hc : Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      densityMargin a b (finePairDensityAtom a b M eu.1.2.1).1 / b *
        (finePairDensityAtom a b M eu.1.2.1).2) :=
    (measurable_of_countable (fun h : FinePairPacketIndex ι M q =>
      densityMargin a b (finePairDensityAtom a b M h.1).1 / b *
        (finePairDensityAtom a b M h.1).2)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (hψ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem finePairPacketIntercept_mem (a b : ℝ) (hab : a ≤ b) (M q : ℕ)
    (e : Z × FinePairPacketIndex ι M q) : finePairPacketIntercept a b M q e ∈ Icc a b :=
  exteriorNode_mem a b hab (M + 2) e.2.1.1

theorem finePairPacketSlope_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) (M q : ℕ)
    (ψ : Z → ℝ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) (e : Z × FinePairPacketIndex ι M q) :
    |finePairPacketSlope a b M q ψ e| ≤ (b - a) / (4 * b) :=
  finePairDensityReset_slope_bound a b ha hab _ _
    (exteriorNode_mem a b hab.le (M + 2) e.2.1.1) (fineModulationNode_bound e.2.1.2)
    (fun _ : Unit => ψ e.1) () (hψ e.1)

theorem finePairPacketWeight_abs_reflection (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (ζ : Z) (h : FinePairPacketIndex ι M q) :
    |finePairPacketWeight a b M q C A (ζ, finePairPacketReflection ι M q h)| =
      |finePairPacketWeight a b M q C A (ζ, h)| := by
  simp only [finePairPacketWeight, finePairDensityWeight, finePairPacketReflection,
    Equiv.prodCongr_apply, Prod.map_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, Fin.revPerm_apply, abs_mul,
    fineModulationWeight_abs_reflection]

theorem finePairPacketSlope_reflection (a b : ℝ) (M q : ℕ) (ψ : Z → ℝ) (ζ : Z)
    (h : FinePairPacketIndex ι M q) :
    finePairPacketSlope a b M q ψ (ζ, finePairPacketReflection ι M q h) =
      -finePairPacketSlope a b M q ψ (ζ, h) := by
  simp only [finePairPacketSlope, finePairPacketIntercept, finePairDensityAtom,
    finePairPacketReflection, Equiv.prodCongr_apply, Prod.map_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, Fin.revPerm_apply,
    fineModulationNode_reflection]
  ring

theorem finePairPacketSlope_absolute_sum_zero (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (ψ : Z → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, |finePairPacketWeight a b M q C A (ζ, h)| *
      finePairPacketSlope a b M q ψ (ζ, h)) = 0 :=
  finite_even_odd_sum_zero (finePairPacketReflection ι M q) _ _
    (finePairPacketWeight_abs_reflection a b M q C A ζ)
    (finePairPacketSlope_reflection a b M q ψ ζ)

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
  (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < finePairPacketMarkMass σ a b M q C A)
include hA hcost hpos

theorem finePairPacketAbsoluteLaw_probability :
    IsProbabilityMeasure (finePairPacketAbsoluteLaw σ a b M q C A) :=
  absoluteMarkLaw_probability _ _ (finePairPacketWeight_integrable σ a b M q C A hA hcost) hpos

theorem finePairPacketMarkMass_eq_variation : finePairPacketMarkMass σ a b M q C A =
    ((finePairPacketSignedMeasure σ a b M q C A).variation univ).toReal :=
  signedMarkMass_eq_variation _ _ (finePairPacketWeight_integrable σ a b M q C A hA hcost)

theorem finePairPacketActivation_bound (e : Z × FinePairPacketIndex ι M q) :
    |finePairPacketActivation σ a b M q C A e| ≤ finePairPacketMarkMass σ a b M q C A :=
  absoluteActivation_bound _ _ e

theorem finePairPacketActivation_centered :
    (∫ e, finePairPacketActivation σ a b M q C A e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  apply absoluteActivation_centered _ _ (finePairPacketWeight_measurable a b M q C A hA) hpos
  rw [integral_prod _ (finePairPacketWeight_integrable σ a b M q C A hA hcost)]
  simp only [integral_count]
  have hz (ζ : Z) : (∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h)) = 0 := by
    have hh := finePairPacketObservable_finite_action a b M q C A (fun _ => 0)
      (fun _ _ _ => 1) (fun _ => 1) ζ
    simpa only [finePairPacketObservable, mul_one, responseMatrixAction_zero_mass, mul_zero] using hh
  simp only [hz, integral_zero]

theorem finePairPacketAbsoluteLaw_slope_integral_zero (ha : 0 < a) (hab : a < b)
    (ψ : Z → ℝ) (hmψ : Measurable ψ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) :
    (∫ e, finePairPacketSlope a b M q ψ e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  have hi := (finePairPacketWeight_integrable σ a b M q C A hA hcost).abs.mul_bdd
    (finePairPacketSlope_measurable a b M q ψ hmψ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using finePairPacketSlope_bound a b ha hab M q ψ hψ e))
  rw [finePairPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    (finePairPacketWeight_measurable a b M q C A hA) hpos, integral_prod _ hi]
  simp only [integral_count, finePairPacketSlope_absolute_sum_zero, integral_zero, zero_div]

theorem finePairPacketAbsoluteLaw_intercept_mem (ha : 0 < a) (hab : a < b) :
    (∫ e, finePairPacketIntercept a b M q e ∂finePairPacketAbsoluteLaw σ a b M q C A) ∈ Icc a b := by
  letI := finePairPacketAbsoluteLaw_probability σ a b M q C A hA hcost hpos
  exact boundedIntercept_mean_mem _ _ (finePairPacketIntercept_measurable a b M q) a b
    (finePairPacketIntercept_mem a b hab.le M q)

end Packet
end NearlyMinimax
