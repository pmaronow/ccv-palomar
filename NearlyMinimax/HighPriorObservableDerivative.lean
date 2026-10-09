module

public import NearlyMinimax.HighRawObservableDerivative


@[expose] public section

/-! Actual high-prior observable derivative: signed append generator plus variance heat. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_rawObservable_hasDerivAt (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba t : ℝ) (ht : 0 < t) (htT : t < T) (hBa : 0 ≤ Ba)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    {d : ℕ} (n : ℕ) (a v η P B : ℝ) (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Ioo 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    HasDerivAt (fun u => ∫ ω, highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
      ∂historyMarkedPrior dependent Δ u π activation)
      ((-η ^ 2 * ∫ ω, highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H
        ∂historyMarkedPrior dependent Δ t π activation) +
        historyMarkedPriorGenerator dependent hsymm Δ t π activation
          (fun ω => highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H)) t := by
  let G : ℝ → HistoryMarked dependent E → ℝ := fun u ω =>
    highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
  let G' : ℝ → HistoryMarked dependent E → ℝ := fun u ω =>
    -η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) H
  let M : ℝ := B * P ^ n * (highSampleReference d n).real Set.univ
  let M' : ℝ := η ^ 2 * (B * (P ^ n * ((n : ℝ) / a ^ 2)) * (highSampleReference d n).real Set.univ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hM' : 0 ≤ M' := by dsimp [M']; positivity
  have hGM (u : ℝ) : Measurable (G u) := highRawObservable_measurable n a (v - η ^ 2 * u) p F hp hF H hH
  have hG'M (u : ℝ) : Measurable (G' u) :=
    (highRawObservableVarianceDerivative_measurable n a (v - η ^ 2 * u) p F hp hF H hH).const_mul (-η ^ 2)
  have hGb (u : ℝ) (hu : u ∈ Ioo 0 T) (ω : HistoryMarked dependent E) : |G u ω| ≤ M :=
    highRawObservable_abs_le n a (v - η ^ 2 * u) P B hP hB (p ω) (F ω) (hpb ω)
      ha.ne' (hq u hu ω) H hHb
  have hG'b (u : ℝ) (hu : u ∈ Ioo 0 T) (ω : HistoryMarked dependent E) : |G' u ω| ≤ M' := by
    change |-η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) H| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul_of_nonneg_left (highRawObservableVarianceDerivative_abs_le n a (v - η ^ 2 * u)
      P B ha hP hB (p ω) (F ω) (hpb ω) (hq u hu ω) H hHb) (sq_nonneg η)
  have hGD (ω : HistoryMarked dependent E) (u : ℝ) (hu : u ∈ Ioo 0 T) :
      HasDerivAt (fun w => G w ω) (G' u ω) u :=
    highRawObservable_hasDerivAt_path n a v η u T P B ha hu.1 hu.2 hP hB p F hp hF hpb hq H hH hHb ω
  have h := historyMarkedPrior_observable_product_rule dependent hrefl hsymm Δ hΔ hlabels
    T Ba t ht htT hBa π activation hactivation habound hsmall G G' hGM hG'M M M' hM hM' hGb hG'b hGD
  simpa only [G, G', integral_const_mul] using h

end NearlyMinimax
