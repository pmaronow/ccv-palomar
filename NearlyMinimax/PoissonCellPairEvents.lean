module

public import NearlyMinimax.PoissonCellField


@[expose] public section

/-! Joint same-cell probabilities under the constructed field law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

def pairSameIndicator (ρ : H → X → Fin 2) (x y : X) (h : H) : ℝ :=
  if ρ h x = ρ h y then 1 else 0

theorem pairSameIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (x y : X) :
    Measurable (pairSameIndicator ρ x y) := by
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (hρ.comp (measurable_id.prodMk measurable_const))
      (hρ.comp (measurable_id.prodMk measurable_const))
  · exact measurable_const
  · exact measurable_const

theorem pairSameIndicator_integrable (μ : Measure H) [IsFiniteMeasure μ]
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (x y : X) :
    Integrable (pairSameIndicator ρ x y) μ :=
  Integrable.of_bound (pairSameIndicator_measurable ρ hρ x y).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun h => by
      unfold pairSameIndicator
      split_ifs <;> norm_num))

def partitionBothProbability (μ : Measure H) (ρ : H → X → Fin 2) (a b c e : X) : ℝ :=
  ∫ h, pairSameIndicator ρ a b h * pairSameIndicator ρ c e h ∂μ

def partitionFiberBothIndicator (ρ : H → X → Fin 2) (n : ℕ)
    (a b c e : X) (h : Fin n → H) : ℝ :=
  if partitionFieldPattern ρ h a = partitionFieldPattern ρ h b ∧
    partitionFieldPattern ρ h c = partitionFieldPattern ρ h e then 1 else 0

theorem partitionFiberBothIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) (a b c e : X) :
    Measurable (partitionFiberBothIndicator ρ n a b c e) := by
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
    · exact measurableSet_eq_fun
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
  · exact measurable_const
  · exact measurable_const

theorem partitionFiberBothIndicator_integral (μ : Measure H) [IsProbabilityMeasure μ]
    (ρ : H → X → Fin 2) (n : ℕ) (a b c e : X) :
    (∫ h, partitionFiberBothIndicator ρ n a b c e h
      ∂Measure.pi (fun _ : Fin n => μ)) = partitionBothProbability μ ρ a b c e ^ n := by
  have he (h : Fin n → H) : partitionFiberBothIndicator ρ n a b c e h =
      ∏ i : Fin n, pairSameIndicator ρ a b (h i) * pairSameIndicator ρ c e (h i) := by
    have hh (z : H) : pairSameIndicator ρ a b z * pairSameIndicator ρ c e z =
        if ρ z a = ρ z b ∧ ρ z c = ρ z e then (1 : ℝ) else 0 := by
      unfold pairSameIndicator
      split_ifs <;> norm_num <;> aesop
    simp_rw [hh]
    unfold partitionFiberBothIndicator
    rw [Fintype.prod_boole]
    simp only [partitionFieldPattern, funext_iff, forall_and]
  simp_rw [he]
  rw [integral_fintype_prod_eq_pow
    (fun h => pairSameIndicator ρ a b h * pairSameIndicator ρ c e h)]
  simp only [partitionBothProbability, Fintype.card_fin]

def poissonCellBothIndicator (ρ : H → X → Fin 2) (a b c e : X)
    (z : partitionFieldMark H) : ℝ := partitionFiberBothIndicator ρ z.1 a b c e z.2.1

theorem poissonCellBothIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (a b c e : X) :
    Measurable (poissonCellBothIndicator ρ a b c e) :=
  measurable_sigma_of_fibers _ (fun n =>
    (partitionFiberBothIndicator_measurable ρ hρ n a b c e).comp measurable_fst)

theorem poissonCellBothIndicator_integral (μ : Measure H) [IsProbabilityMeasure μ]
    (r : ℝ≥0) (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (a b c e : X) :
    (∫ z, poissonCellBothIndicator ρ a b c e z ∂poissonCellFieldLaw μ r) =
      Real.exp (-(r : ℝ) * (1 - partitionBothProbability μ ρ a b c e)) := by
  rw [poissonCellField_integral_series μ r _
    (poissonCellBothIndicator_measurable ρ hρ a b c e)
    (fun z => by unfold poissonCellBothIndicator partitionFiberBothIndicator
                 split_ifs <;> norm_num)]
  have hf (n : ℕ) : (∫ z : partitionFieldFiber H n,
      poissonCellBothIndicator ρ a b c e ⟨n, z⟩ ∂partitionFieldFiberLaw μ n) =
      partitionBothProbability μ ρ a b c e ^ n := by
    change (∫ z : (Fin n → H) × ((Fin n → Fin 2) → Fin 2),
      partitionFiberBothIndicator ρ n a b c e z.1
      ∂(Measure.pi (fun _ : Fin n => μ)).prod (cellSignLaw (Fin n → Fin 2))) = _
    rw [integral_fun_fst]
    simpa using partitionFiberBothIndicator_integral μ ρ n a b c e
  simp_rw [hf]
  exact (poisson_weighted_power_hasSum r _).tsum_eq

end NearlyMinimax
