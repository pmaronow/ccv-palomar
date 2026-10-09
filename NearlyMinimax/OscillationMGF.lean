module

public import Mathlib


@[expose] public section

/-!
# Genuine Hoeffding bound from pairwise oscillation
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace NearlyMinimax

variable {E : Type*} [MeasurableSpace E]

/-- Pairwise oscillation yields the exact range-length version of Hoeffding's lemma.
The range endpoints are actual infimum and supremum; no concentration conclusion is assumed. -/
theorem centered_mgf_le_of_oscillation (π : Measure E) [IsProbabilityMeasure π] [Nonempty E]
    (X : E → ℝ) (hX : Measurable X) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ e, |X e| ≤ R) (hosc : ∀ e f, |X e - X f| ≤ c) (u : ℝ) :
    (∫ e, Real.exp (u * (X e - ∫ f, X f ∂π)) ∂π) ≤ Real.exp (u ^ 2 * c ^ 2 / 8) := by
  let S := Set.range X
  have hne : S.Nonempty := Set.range_nonempty X
  have hbelow : BddBelow S := ⟨-R, by rintro z ⟨e, rfl⟩; exact (abs_le.1 (hbound e)).1⟩
  have habove : BddAbove S := ⟨R, by rintro z ⟨e, rfl⟩; exact (abs_le.1 (hbound e)).2⟩
  have hx : ∀ e, X e ∈ Icc (sInf S) (sSup S) := by
    intro e
    exact ⟨csInf_le hbelow ⟨e, rfl⟩, le_csSup habove ⟨e, rfl⟩⟩
  have hrange : sSup S - sInf S ≤ c := by
    have hh : sSup S ≤ sInf S + c := by
      apply csSup_le hne
      rintro z ⟨e, rfl⟩
      have hl : X e - c ≤ sInf S := by
        apply le_csInf hne
        rintro z ⟨f, rfl⟩
        have hh := (abs_le.1 (hosc e f)).2
        linarith
      linarith
    linarith
  have horder : 0 ≤ sSup S - sInf S := sub_nonneg.2 (csInf_le_csSup hne hbelow habove)
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := π) (X := X)
    (a := sInf S) (b := sSup S) hX.aemeasurable (Eventually.of_forall hx)
  have hh := hsg.mgf_le u
  have hexp : (((‖sSup S - sInf S‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * u ^ 2 / 2 ≤ u ^ 2 * c ^ 2 / 8 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat, abs_of_nonneg horder]
    have hsq : (sSup S - sInf S) ^ 2 ≤ c ^ 2 := (sq_le_sq₀ horder hc).2 hrange
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg u)]
  exact hh.trans (Real.exp_le_exp.2 hexp)

end NearlyMinimax
