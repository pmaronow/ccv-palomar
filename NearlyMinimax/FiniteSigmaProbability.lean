module

public import Mathlib


@[expose] public section

/-! Measurability and standard Borel structure of the finite disjoint mark
families used in the actual separated cardinal kernel. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem measurable_sigma_mk_actual {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (i : ι) : Measurable (Sigma.mk i : E i → Sigma E) := by
  apply Measurable.of_le_map
  exact iInf_le _ i

theorem measurable_sigma_of_fibers {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] {X : Type*} [MeasurableSpace X]
    (f : Sigma E → X) (hf : ∀ i, Measurable (fun e : E i => f ⟨i, e⟩)) : Measurable f := by
  apply Measurable.of_le_map
  change _ ≤ (⨅ i, (inferInstance : MeasurableSpace (E i)).map (Sigma.mk i)).map f
  rw [MeasurableSpace.map_iInf]
  apply le_iInf
  intro i
  rw [MeasurableSpace.map_comp]
  exact (hf i).le_map

/-- A countable disjoint union of Borel spaces has precisely the Borel
sigma-algebra of its disjoint-union topology. -/
theorem sigma_borelSpace_actual {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] :
    BorelSpace (Sigma E) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hfiber (i : ι) : MeasurableSet (Sigma.mk i ⁻¹' s) :=
      hs.preimage (measurable_sigma_mk_actual i)
    have himage (i : ι) : MeasurableSet[borel (Sigma E)] (Sigma.mk i '' (Sigma.mk i ⁻¹' s)) := by
      letI : MeasurableSpace (Sigma E) := borel (Sigma E)
      letI : BorelSpace (Sigma E) := ⟨rfl⟩
      exact (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image).mpr (hfiber i)
    have he : s = ⋃ i : ι, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
      ext z
      constructor
      · intro hz
        exact mem_iUnion.mpr ⟨z.1, ⟨z.2, hz, Sigma.eta z⟩⟩
      · intro hz
        rcases mem_iUnion.mp hz with ⟨i, hi⟩
        rcases hi with ⟨e, he, rfl⟩
        exact he
    rw [he]
    exact MeasurableSet.iUnion himage
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    change MeasurableSet[(⨅ i, (inferInstance : MeasurableSpace (E i)).map (Sigma.mk i))] s
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro i
    change MeasurableSet (Sigma.mk i ⁻¹' s)
    exact (hs.preimage continuous_sigmaMk).measurableSet

/-- Standard Borel structure is inherited by the actual disjoint mark
family; the proof supplies a compatible Polish topology. -/
theorem sigma_standardBorel_actual {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] : StandardBorelSpace (Sigma E) := by
  letI : ∀ i, TopologicalSpace (E i) := fun i => (upgradeStandardBorel (E i)).toTopologicalSpace
  letI : ∀ i, BorelSpace (E i) := fun i => (upgradeStandardBorel (E i)).toBorelSpace
  letI : ∀ i, PolishSpace (E i) := fun i => (upgradeStandardBorel (E i)).toPolishSpace
  letI : BorelSpace (Sigma E) := sigma_borelSpace_actual
  infer_instance

end NearlyMinimax
