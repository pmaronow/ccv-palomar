module

public import Mathlib


@[expose] public section

/-! The manuscript's norm takes a supremum over nuisance values before
spatial integration.  These lemmas prove that the actual compact supremum
is measurable and integrable from separate Borel measurability, nuisance
continuity, and a genuine integrable universal spatial envelope. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section Generic
variable {P X Y : Type*} [TopologicalSpace P] [SecondCountableTopology P]
  [MeasurableSpace X] [Fintype Y]

def compactNuisanceEnergy (K : Set P) (F : P → X → Y → ℝ) (x : X) : ℝ :=
  sSup ((fun p => ∑ y, (F p x y) ^ 2) '' K)

theorem compactNuisanceEnergy_attained (K : Set P) (hK : IsCompact K)
    (hKn : K.Nonempty) (F : P → X → Y → ℝ)
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K) (x : X) :
    ∃ p ∈ K, compactNuisanceEnergy K F x = ∑ y, (F p x y) ^ 2 ∧
      ∀ q ∈ K, (∑ y, (F q x y) ^ 2) ≤ ∑ y, (F p x y) ^ 2 := by
  exact hK.exists_sSup_image_eq_and_ge hKn
    (continuousOn_finsetSum _ (fun y _ => (hcont x y).pow 2))

theorem compactNuisanceEnergy_nonneg (K : Set P) (hK : IsCompact K)
    (hKn : K.Nonempty) (F : P → X → Y → ℝ)
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K) (x : X) :
    0 ≤ compactNuisanceEnergy K F x := by
  obtain ⟨p, _, hp, _⟩ := compactNuisanceEnergy_attained K hK hKn F hcont x
  rw [hp]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem compactNuisanceEnergy_le (K : Set P) (hK : IsCompact K)
    (hKn : K.Nonempty) (F : P → X → Y → ℝ)
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K)
    (H : X → ℝ) (hbound : ∀ p ∈ K, ∀ x, (∑ y, (F p x y) ^ 2) ≤ H x)
    (x : X) : compactNuisanceEnergy K F x ≤ H x := by
  obtain ⟨p, hpK, hp, _⟩ := compactNuisanceEnergy_attained K hK hKn F hcont x
  rw [hp]
  exact hbound p hpK x

/-- The real compact supremum is exactly the real value of the measurable
extended-real supremum; compactness rules out an infinite value. -/
theorem compactNuisanceEnergy_eq_ennreal_sup (K : Set P) (hK : IsCompact K)
    (hKn : K.Nonempty) (F : P → X → Y → ℝ)
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K) (x : X) :
    compactNuisanceEnergy K F x =
      (⨆ p : K, ENNReal.ofReal (∑ y, (F p.val x y) ^ 2)).toReal := by
  obtain ⟨p, hpK, hp, hmax⟩ := compactNuisanceEnergy_attained K hK hKn F hcont x
  have hs : (⨆ q : K, ENNReal.ofReal (∑ y, (F q.val x y) ^ 2)) =
      ENNReal.ofReal (∑ y, (F p x y) ^ 2) := by
    apply le_antisymm
    · exact iSup_le (fun q => ENNReal.ofReal_le_ofReal (hmax q.val q.property))
    · exact le_iSup_of_le ⟨p, hpK⟩ le_rfl
  rw [hs, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact hp

theorem compactNuisanceEnergy_measurable (K : Set P) (hK : IsCompact K)
    (hKn : K.Nonempty) (F : P → X → Y → ℝ)
    (hmeas : ∀ p ∈ K, ∀ y, Measurable (fun x => F p x y))
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K) :
    Measurable (compactNuisanceEnergy K F) := by
  have hm : ∀ p : K, Measurable (fun x =>
      ENNReal.ofReal (∑ y, (F p.val x y) ^ 2)) := by
    intro p
    exact (Finset.measurable_sum _ (fun y _ =>
      (hmeas p.val p.property y).pow_const 2)).ennreal_ofReal
  have hc : ∀ x, LowerSemicontinuous (fun p : K =>
      ENNReal.ofReal (∑ y, (F p.val x y) ^ 2)) := by
    intro x
    exact (ENNReal.continuous_ofReal.comp
      (continuous_finsetSum _ (fun y _ => ((hcont x y).domRestrict).pow 2))).lowerSemicontinuous
  have hs := (measurable_iSup_of_lowerSemicontinuous hm hc).ennreal_toReal
  simp only [iSup_apply] at hs
  have he : compactNuisanceEnergy K F = (fun x =>
      (⨆ p : K, ENNReal.ofReal (∑ y, (F p.val x y) ^ 2)).toReal) := by
    funext x
    exact compactNuisanceEnergy_eq_ennreal_sup K hK hKn F hcont x
  rwa [← he] at hs

theorem compactNuisanceEnergy_integrable_and_bound (μ : Measure X)
    (K : Set P) (hK : IsCompact K) (hKn : K.Nonempty)
    (F : P → X → Y → ℝ)
    (hmeas : ∀ p ∈ K, ∀ y, Measurable (fun x => F p x y))
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K)
    (H : X → ℝ) (hH : Integrable H μ)
    (hbound : ∀ p ∈ K, ∀ x, (∑ y, (F p x y) ^ 2) ≤ H x) :
    Integrable (compactNuisanceEnergy K F) μ ∧
      (∫ x, compactNuisanceEnergy K F x ∂μ) ≤ ∫ x, H x ∂μ := by
  have hm := compactNuisanceEnergy_measurable K hK hKn F hmeas hcont
  have hb (x) := compactNuisanceEnergy_le K hK hKn F hcont H hbound x
  have hi : Integrable (compactNuisanceEnergy K F) μ := by
    apply hH.mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (compactNuisanceEnergy_nonneg K hK hKn F hcont x)]
      exact hb x)
  exact ⟨hi, integral_mono hi hH hb⟩

end Generic
end NearlyMinimax
