module

public import NearlyMinimax.HighPatchProductMeasure
public import NearlyMinimax.HighPatchChartExact


@[expose] public section

/-! Exact finite product chart Jacobian bounds, with the original h^d
coefficient and no wrapping multiplicity loss. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true iid product-chart law is dominated by the cardinal power of
its one-point Jacobian bound. -/
theorem highPatchProductChart_map_le_exact {I : Type*} [Fintype I] {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) :
    Measure.map (highPatchProductChart (I := I) d k j)
      (Measure.pi (fun _ : I => (cubeVolume d).restrict (highTorusPatch d k j))) ≤
    ENNReal.ofReal (((1/(k : ℝ))^d)^(Fintype.card I)) •
      Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d)) := by
  letI := cubeVolume_isProbability d
  letI := (volume.restrict (spatialPatchBox d)).smul_finite
    (c := ENNReal.ofReal ((1/(k : ℝ))^d)) ENNReal.ofReal_ne_top
  change Measure.map (fun x : I → Covariate d => fun i => highLocalCoordinates d k j (x i)) _ ≤ _
  rw [Measure.pi_map_pi (fun _ => (highLocalCoordinates_measurable d k j).aemeasurable)]
  calc
    _ ≤ Measure.pi (fun _ : I => ENNReal.ofReal ((1/(k : ℝ))^d) •
      volume.restrict (spatialPatchBox d)) :=
      finite_pi_measure_mono _ _ (fun _ => highLocalCoordinates_patch_map_le_exact hk j)
    _ = _ := by
      rw [spatialPi_const_smul, ← ENNReal.ofReal_pow (by positivity)]

/-- Genuine integrability after all selected points are placed in the
actual periodic torus chart. -/
theorem highPatchProductChart_integrable_exact {I : Type*} [Fintype I] {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (H : (I → Covariate d) → ℝ)
    (hH : Integrable H (Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d)))) :
    Integrable (fun x => H (highPatchProductChart d k j x))
      (Measure.pi (fun _ : I => (cubeVolume d).restrict (highTorusPatch d k j))) := by
  have hm : Integrable H (Measure.map (highPatchProductChart d k j)
      (Measure.pi (fun _ : I => (cubeVolume d).restrict (highTorusPatch d k j)))) :=
    (hH.smul_measure ENNReal.ofReal_ne_top).mono_measure (highPatchProductChart_map_le_exact hk j)
  exact hm.comp_measurable (highPatchProductChart_measurable d k j)

/-- Actual nonnegative real integral comparison for the selected spatial
score numerators under independent original covariates. -/
theorem highPatchProductChart_integral_le_exact {I : Type*} [Fintype I] {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (H : (I → Covariate d) → ℝ)
    (hH : Integrable H (Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ x, 0 ≤ H x) :
    (∫ x, H (highPatchProductChart d k j x)
      ∂Measure.pi (fun _ : I => (cubeVolume d).restrict (highTorusPatch d k j))) ≤
    (((1/(k : ℝ))^d)^(Fintype.card I)) *
      ∫ u, H u ∂Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d)) := by
  have hs := hH.smul_measure (c := ENNReal.ofReal (((1/(k : ℝ))^d)^(Fintype.card I)))
    ENNReal.ofReal_ne_top
  have hm := hs.mono_measure (highPatchProductChart_map_le_exact hk j)
  rw [← integral_map (highPatchProductChart_measurable d k j).aemeasurable hm.aestronglyMeasurable]
  calc
    _ ≤ ∫ x, H x ∂ENNReal.ofReal (((1/(k : ℝ))^d)^(Fintype.card I)) •
        Measure.pi (fun _ : I => volume.restrict (spatialPatchBox d)) :=
      integral_mono_measure (highPatchProductChart_map_le_exact hk j)
        (Filter.Eventually.of_forall hH0) hs
    _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

end NearlyMinimax
