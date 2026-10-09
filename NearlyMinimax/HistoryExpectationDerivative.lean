module

public import NearlyMinimax.HistoryDensityDerivative


@[expose] public section

/-!
# Differentiating actual marked-history expectations
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The expectation weighted by the actual source history polynomial. -/
def historyMarkedExpectation (dependent : J → J → Prop) (ρ : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E))
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) (t : ℝ) : ℝ :=
  ∫ h, F h * historyMarkedDensity dependent ρ t a h ∂μ

/-- A bounded measurable observable has a genuine derivative under the finite reference law.
The uniform majorant is proved from maximal-label injectivity and source positivity. -/
theorem historyMarkedExpectation_hasDerivAt (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B t : ℝ) (hρ : 0 < ρ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsFiniteMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    Integrable (fun h => F h * historyMarkedDensityDerivative dependent ρ t a h) μ ∧
      HasDerivAt (historyMarkedExpectation dependent ρ μ a F)
        (∫ h, F h * historyMarkedDensityDerivative dependent ρ t a h ∂μ) t := by
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have hC : 0 ≤ C := by positivity
  have hs : ∀ u ∈ Ioo 0 T, u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) := by
    intro u hu
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB) hρ.le).trans hsmall
  have hbound : ∀ u ∈ Ioo 0 T, ∀ h : HistoryMarked dependent E,
      |F h * historyMarkedDensityDerivative dependent ρ u a h| ≤ M * D := by
    intro u hu h
    rw [abs_mul]
    exact mul_le_mul (hFbound h)
      (historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1.le hB
        a habound (hs u hu) h) (abs_nonneg _) hM
  have hFM : ∀ u, Measurable (fun h => F h * historyMarkedDensity dependent ρ u a h) :=
    fun u => hF.mul (historyMarkedDensity_measurable dependent ρ u a ha)
  have hDM : ∀ u, Measurable (fun h => F h * historyMarkedDensityDerivative dependent ρ u a h) :=
    fun u => hF.mul (historyMarkedDensityDerivative_measurable dependent ρ u a ha)
  have hInt : Integrable (fun h => F h * historyMarkedDensity dependent ρ t a h) μ := by
    apply Integrable.of_bound (hFM t).aestronglyMeasurable (M * C)
    apply Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_mul]
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht.le hB
      a habound (hs t ⟨ht, htT⟩) h
    have hn : 0 ≤ historyMarkedDensity dependent ρ t a h :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hn]
    exact mul_le_mul (hFbound h) hb.2 hn hM
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun u h => F h * historyMarkedDensity dependent ρ u a h)
    (F' := fun u h => F h * historyMarkedDensityDerivative dependent ρ u a h)
    (bound := fun _ => M * D) (s := Ioo 0 T)
    (Ioo_mem_nhds ht htT) (Eventually.of_forall fun u => (hFM u).aestronglyMeasurable)
    hInt (hDM t).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => by simpa only [Real.norm_eq_abs] using hbound u hu h)
    (integrable_const (M * D))
    (Eventually.of_forall fun h u _ => (historyMarkedDensity_hasDerivAt dependent ρ u a h).const_mul (F h))

end NearlyMinimax
