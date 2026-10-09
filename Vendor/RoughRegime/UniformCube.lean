module

public import RoughRegime.Model


@[expose] public section

/-! The actual unit-cube Lebesgue design is a probability measure, also for
dimension zero. Its coordinate law is the product of one-dimensional uniforms. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RoughRegime.Model

theorem cube_eq_preimage (d : ℕ) : cube d =
    (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' pi univ (fun _ : Fin d => Icc (0 : ℝ) 1) := by
  ext x
  simp only [cube, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, true_implies]

theorem measurableSet_cube (d : ℕ) : MeasurableSet (cube d) := by
  rw [cube_eq_preimage]
  exact (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem volume_cube (d : ℕ) : volume (cube d) = 1 := by
  rw [cube_eq_preimage,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc).nullMeasurableSet]
  simp [Real.volume_Icc_pi]

instance cubeVolume_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (cubeVolume d) where
  measure_univ := by simp [cubeVolume, volume_cube]

def uniformCube (d : ℕ) : ProbabilityMeasure (Covariate d) :=
  ⟨cubeVolume d, inferInstance⟩

end RoughRegime.Model
