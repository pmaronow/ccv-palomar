module

public import NearlyMinimax.ProductBoundedDifferences


@[expose] public section

/-!
# Genuine independent label blocks for the actual finite history marks
-/

noncomputable section
open MeasureTheory Set
namespace NearlyMinimax

variable {J I E : Type*} [Fintype J] [Fintype I] [MeasurableSpace E]

/-- Reconstruct each actual occurrence mark from the independent vector for its true label.
Unused coordinates give a harmless redundant realization of independent finite label blocks. -/
def labelBlockReconstruct (labels : I → J) (blocks : J → I → E) : I → E :=
  fun i => blocks (labels i) i

omit [Fintype J] [Fintype I] in
/-- The actual label-block reconstruction is jointly measurable. -/
theorem labelBlockReconstruct_measurable (labels : I → J) :
    Measurable (labelBlockReconstruct labels (E := E)) := by
  apply measurable_pi_iff.2
  intro i
  exact (measurable_pi_apply i).comp (measurable_pi_apply (labels i))

/-- Redundant independent label vectors reproduce exactly the original independent occurrence marks. -/
theorem labelBlockReconstruct_preserving (labels : I → J) (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (labelBlockReconstruct labels (E := E))
      (Measure.pi (fun _ : J => Measure.pi (fun _ : I => π)))
      (Measure.pi (fun _ : I => π)) := by
  classical
  refine ⟨labelBlockReconstruct_measurable labels, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : I => π) ?_).symm
  intro s hs
  rw [Measure.map_apply (labelBlockReconstruct_measurable labels) (MeasurableSet.univ_pi hs)]
  have hp : labelBlockReconstruct labels ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun j : J => Set.univ.pi (fun i : I => if labels i = j then s i else Set.univ)) := by
    ext blocks
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, labelBlockReconstruct]
    constructor
    · intro h j i
      by_cases hij : labels i = j
      · simpa only [hij, ite_true] using h i
      · simp only [hij, ite_false, Set.mem_univ]
    · intro h i
      simpa only [ite_true] using h (labels i) i
  rw [hp, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  have he : ∀ j i, π (if labels i = j then s i else Set.univ) =
      if labels i = j then π (s i) else 1 := by
    intro j i
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  simp

omit [Fintype J] [Fintype I] [MeasurableSpace E] in
/-- Replacing a label block leaves every occurrence of another label exactly unchanged. -/
theorem labelBlockReconstruct_update_other [DecidableEq J] (labels : I → J) (blocks : J → I → E)
    (j : J) (new : I → E) (i : I) (hi : labels i ≠ j) :
    labelBlockReconstruct labels (Function.update blocks j new) i = labelBlockReconstruct labels blocks i := by
  classical
  simp [labelBlockReconstruct, Function.update_of_ne hi]

end NearlyMinimax
