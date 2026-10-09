module

public import NearlyMinimax.CoordinatePartialBridge


@[expose] public section

/-! The manuscript's `L∞` convention agrees exactly with the pointwise
derivative suprema in the formal model, because the extension domain is
open and all derivatives being measured are continuous there. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
namespace NearlyMinimax

theorem continuousOn_ennreal_essSup_eq {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X)
    [μ.IsOpenPosMeasure] (U : Set X) (hU : IsOpen U)
    (f : X → ℝ≥0∞) (hf : ContinuousOn f U) :
    essSup f (μ.restrict U) = ⨆ x : U, f x := by
  apply le_antisymm
  · refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact le_iSup_of_le ⟨x, hx⟩ le_rfl
  · have hae : f =ᵐ[μ.restrict U] fun x => min (f x) (essSup f (μ.restrict U)) := by
      filter_upwards [ENNReal.ae_le_essSup f] with x hx
      exact (min_eq_left hx).symm
    have he := Measure.eqOn_open_of_ae_eq hae hU hf (hf.inf continuousOn_const)
    apply iSup_le
    intro x
    calc
      f x = min (f x) (essSup f (μ.restrict U)) := he x.property
      _ ≤ _ := min_le_right _ _

theorem derivativeSup_eq_essSup {d : ℕ} (U : Set (Covariate d)) (hU : IsOpen U)
    (G : Covariate d → ℝ) (hG : ContinuousOn G U) :
    derivativeSup U G = essSup (fun x => ENNReal.ofReal |G x|) (volume.restrict U) := by
  exact (continuousOn_ennreal_essSup_eq volume U hU _
    (ENNReal.continuous_ofReal.comp_continuousOn hG.abs)).symm

theorem multiPartial_continuousOn {d ℓ : ℕ} (U : Set (Covariate d)) (hU : IsOpen U)
    (F : Covariate d → ℝ) (hf : ContDiffOn ℝ ℓ F U)
    (γ : Fin d → ℕ) (hγ : (∑ i, γ i) ≤ ℓ) : ContinuousOn (multiPartial F γ) U := by
  have hd : ContinuousOn (iteratedFDeriv ℝ (∑ i, γ i) F) U :=
    ContinuousOn.continuousOn_iteratedFDeriv hf hU (by exact_mod_cast hγ)
  have he : ContinuousOn
      (fun x => iteratedFDeriv ℝ (∑ i, γ i) F x (multiIndexBasis γ)) U :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, γ i) => Covariate d) ℝ
      (multiIndexBasis γ)).continuous.comp_continuousOn hd
  exact he.congr (fun x hx => multiPartial_eq_iteratedFDeriv U hU F ℓ hf γ hγ x hx)

def essentialHolderNorm {d : ℕ} (U : Set (Covariate d)) (F : Covariate d → ℝ)
    (ℓ : ℕ) (α : ℝ) : ℝ≥0∞ :=
  (∑ γ : Fin d → Fin (ℓ + 1),
    if (∑ i, (γ i).val) ≤ ℓ then
      essSup (fun x => ENNReal.ofReal |multiPartial F (fun i => (γ i).val) x|)
        (volume.restrict U) else 0) +
  ⨆ γ : Fin d → Fin (ℓ + 1),
    if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α else 0

theorem holderNorm_eq_essentialHolderNorm {d ℓ : ℕ} (U : Set (Covariate d))
    (hU : IsOpen U) (F : Covariate d → ℝ) (α : ℝ)
    (hf : ContDiffOn ℝ ℓ F U) :
    holderNorm U F ℓ α = essentialHolderNorm U F ℓ α := by
  classical
  unfold holderNorm essentialHolderNorm
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  split_ifs with hγ
  · exact derivativeSup_eq_essSup U hU _
      (multiPartial_continuousOn U hU F hf (fun i => (γ i).val) hγ)
  · rfl

theorem holderNorm_le_iff_essentialHolderNorm_le {d ℓ : ℕ}
    (U : Set (Covariate d)) (hU : IsOpen U) (F : Covariate d → ℝ) (α : ℝ)
    (hf : ContDiffOn ℝ ℓ F U) (K : ℝ≥0∞) :
    holderNorm U F ℓ α ≤ K ↔ essentialHolderNorm U F ℓ α ≤ K := by
  rw [holderNorm_eq_essentialHolderNorm U hU F α hf]

end NearlyMinimax
