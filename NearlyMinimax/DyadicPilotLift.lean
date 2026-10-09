module

public import NearlyMinimax.PilotCoordinateExpansion
public import NearlyMinimax.KernelMomentBounds


@[expose] public section

/-! Genuine L² data and raw-kernel support for the actual dyadic pilot
under the original iid observation experiment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev localPilotDimension (d ℓ : ℕ) := Fintype.card (LocalPilotIndex d ℓ)

def dyadicPilotRawVector {d ℓ : ℕ} (j : ℕ) (x : Covariate d) (z : Observation d) :
    Fin (localPilotDimension d ℓ) → ℝ :=
  fun a => dyadicPilotFeature j x ((Fintype.equivFin (LocalPilotIndex d ℓ)).symm a) z

def dyadicPilotRawMean {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Fin (localPilotDimension d ℓ) → ℝ :=
  fun a => dyadicPilotPopulation θ j x ((Fintype.equivFin (LocalPilotIndex d ℓ)).symm a)

theorem dyadicPilotRawVector_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    Measurable (dyadicPilotRawVector (ℓ := ℓ) j x) :=
  measurable_pi_iff.mpr (fun _ => dyadicPilotFeature_measurable j x _)

theorem dyadicPilotRawVector_memLp_coordinates {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : Fin (localPilotDimension d ℓ)) :
    MemLp (fun z => dyadicPilotRawVector j x z a) 2 (observationLaw θ) :=
  dyadicPilotFeature_memLp_two C θ hθ j x hx _

theorem dyadicPilotRawVector_second_le {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    (∫ z, ‖dyadicPilotRawVector (ℓ := ℓ) j x z‖ ^ 2 ∂observationLaw θ) ≤
      localPilotDimension d ℓ * dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  apply (KernelMomentBounds.vector_second_le_sum_coordinates
    (dyadicPilotRawVector j x) (dyadicPilotRawVector_measurable j x)
    (dyadicPilotRawVector_memLp_coordinates C θ hθ j x hx)).trans
  exact (Finset.sum_le_sum (fun a _ => dyadicPilotFeature_second_le C θ hθ j x hx _)).trans_eq
    (by simp [localPilotDimension, mul_assoc])

/-- The paper's original sample law gives the actual iid/L² mean data for
every concrete dyadic anchor, rather than a substitute bounded experiment. -/
theorem dyadicPilotRawVector_sample_facts {d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    iIndepFun (fun i (z : Fin n → Observation d) => dyadicPilotRawVector (ℓ := ℓ) j x (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => dyadicPilotRawVector (ℓ := ℓ) j x (z i))) ∧
    (∀ i t : Fin n, IdentDistrib
      (fun z : Fin n → Observation d => dyadicPilotRawVector (ℓ := ℓ) j x (z i))
      (fun z : Fin n → Observation d => dyadicPilotRawVector (ℓ := ℓ) j x (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z : Fin n → Observation d => dyadicPilotRawVector (ℓ := ℓ) j x (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, dyadicPilotRawVector (ℓ := ℓ) j x (z i) a ∂sampleLaw θ n) =
      dyadicPilotRawMean θ j x a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := dyadicPilotRawVector_measurable (ℓ := ℓ) j x
  have hp (i : Fin n) : MeasurePreserving (fun z : Fin n → Observation d => z i)
      (sampleLaw θ n) (observationLaw θ) := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi (fun _ : Fin n => hm.aemeasurable),
    fun i => hm.comp (measurable_pi_apply i), ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib (fun z : Fin n → Observation d => z i)
        (fun z : Fin n → Observation d => z t) (sampleLaw θ n) (sampleLaw θ n) :=
      ⟨(hp i).aemeasurable, (hp t).aemeasurable, (hp i).map_eq.trans (hp t).map_eq.symm⟩
    exact ht.comp hm
  · intro i a
    exact (dyadicPilotRawVector_memLp_coordinates C θ hθ j x hx a).comp_measurePreserving (hp i)
  · intro i a
    exact integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i)
      ((dyadicPilotFeature_measurable j x
        ((Fintype.equivFin (LocalPilotIndex d ℓ)).symm a)).aestronglyMeasurable)

theorem dyadicPilotRawVector_zero_off_cell {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (z : Observation d) (hz : z.1 ∉ dyadicPilotCell j x) :
    dyadicPilotRawVector (ℓ := ℓ) j x z = 0 := by
  funext a
  simp [dyadicPilotRawVector, dyadicPilotFeature, hz]

/-- A raw positive-order local kernel vanishes if any one observation is
outside its actual cell. This statement is made before centering. -/
theorem dyadic_raw_kernel_zero_off_cell {d ℓ k : ℕ} (j : ℕ) (x : Covariate d)
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (localPilotDimension d ℓ) → ℝ) ℝ)
    (z : Fin k → Observation d) (i : Fin k) (hz : (z i).1 ∉ dyadicPilotCell j x) :
    H (fun t => dyadicPilotRawVector j x (z t)) = 0 := by
  exact H.map_coord_zero i (dyadicPilotRawVector_zero_off_cell j x (z i) hz)

/-- Distinct actual anchor cells have disjoint support for every positive
raw kernel order, irrespective of the particular derivative coefficients. -/
theorem dyadic_raw_kernels_disjoint {d ℓ k : ℕ} (hk : 0 < k) (j : ℕ) (x y : Covariate d)
    (hcell : dyadicPilotLabel j x ≠ dyadicPilotLabel j y)
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (localPilotDimension d ℓ) → ℝ) ℝ)
    (z : Fin k → Observation d) :
    H (fun t => dyadicPilotRawVector j x (z t)) *
      G (fun t => dyadicPilotRawVector j y (z t)) = 0 := by
  let i : Fin k := ⟨0, hk⟩
  by_cases hz : (z i).1 ∈ dyadicPilotCell j x
  · have hzy : (z i).1 ∉ dyadicPilotCell j y := by
      intro h
      apply hcell
      exact ((dyadicPilotLabel_eq_iff j x (z i).1).mpr hz).symm.trans
        ((dyadicPilotLabel_eq_iff j y (z i).1).mpr h)
    rw [dyadic_raw_kernel_zero_off_cell j y G z i hzy, mul_zero]
  · rw [dyadic_raw_kernel_zero_off_cell j x H z i hz, zero_mul]

end NearlyMinimax
