module

public import NearlyMinimax.PilotFields
public import Mathlib.MeasureTheory.Measure.SeparableMeasure


@[expose] public section

/-! Jointly Borel scalar kernels define genuine Borel maps into L². This
permits Bochner integration of arbitrary square-integrable kernel fields,
without an assumed finite polynomial or coefficient representation. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

private theorem measurable_of_measurable_dist_to_point {A B : Type*}
    [MeasurableSpace A] [MetricSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B] (f : A → B)
    (hf : ∀ b : B, Measurable (fun a => dist (f a) b)) : Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  let I := {q : B × ℝ // Metric.ball q.1 q.2 ⊆ U}
  let s : I → Set B := fun i => Metric.ball i.1.1 i.1.2
  have hUeq : U = ⋃ i, s i := by
    ext x
    constructor
    · intro hx
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
      exact mem_iUnion.mpr ⟨⟨(x,r), hball⟩, Metric.mem_ball_self hr⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact i.2 hi
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable s (fun _ => Metric.isOpen_ball)
  rw [hUeq, ← hT]
  simp only [preimage_iUnion]
  apply MeasurableSet.biUnion hTc
  intro i _
  exact measurableSet_lt (hf i.1.1) measurable_const

section Fields
variable {W O : Type*} [MeasurableSpace W] [MeasurableSpace O]
  (μ : Measure O) [IsFiniteMeasure μ] [IsSeparable μ]

local instance : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-- The actual L² class of each raw scalar section. -/
def rawKernelSection (K : W → O → ℝ) (hK : ∀ w, MemLp (K w) 2 μ) :
    W → Lp ℝ 2 μ := fun w => (hK w).toLp (K w)

/-- A joint scalar Borel hypothesis implies Borel measurability in the
Bochner L² norm. Separability of μ follows for all standard Borel sample
spaces equipped with their finite original law. -/
theorem rawKernelSection_measurable (K : W → O → ℝ)
    (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ) :
    Measurable (rawKernelSection μ K hK) := by
  apply measurable_of_measurable_dist_to_point
  intro u
  have hu : Measurable (fun z : W × O => u z.2) :=
    (Lp.stronglyMeasurable u).measurable.comp measurable_snd
  have hsq : Measurable (fun z : W × O => (K z.1 z.2 - u z.2)^2) := (hm.sub hu).pow_const 2
  have hi : Measurable (fun w => ∫ o, (K w o - u o)^2 ∂μ) :=
    hsq.stronglyMeasurable.integral_prod_right'.measurable
  have heq (w : W) : dist (rawKernelSection μ K hK w) u =
      Real.sqrt (∫ o, (K w o - u o)^2 ∂μ) := by
    have hf : MemLp (fun o => K w o - u o) 2 μ := (hK w).sub (Lp.memLp u)
    have hclass : hf.toLp (fun o => K w o - u o) = rawKernelSection μ K hK w - u := by
      apply Lp.ext
      filter_upwards [hf.coeFn_toLp, Lp.coeFn_sub (rawKernelSection μ K hK w) u,
        (hK w).coeFn_toLp] with o ho hs hk
      dsimp [rawKernelSection] at hs ⊢
      rw [ho, hs, hk]
    have hnorm := PilotFields.toLp_norm_sq hf
    rw [hclass] at hnorm
    simp only [Real.norm_eq_abs, sq_abs] at hnorm
    rw [← hnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]
  have hfun : (fun w => dist (rawKernelSection μ K hK w) u) =
      (fun w => Real.sqrt (∫ o, (K w o - u o)^2 ∂μ)) := funext heq
  rw [hfun]
  exact hi.sqrt

theorem rawKernelSection_aestronglyMeasurable (M : Measure W) (K : W → O → ℝ)
    (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ) :
    AEStronglyMeasurable (rawKernelSection μ K hK) M :=
  (rawKernelSection_measurable μ K hm hK).aestronglyMeasurable

end Fields
end NearlyMinimax
