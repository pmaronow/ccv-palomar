module

public import NearlyMinimax.Model


@[expose] public section

/-! Cube-defined model objects admit ambient representatives without changing
the regression experiment. The extension uses an explicit continuous cube
retraction; the error kernel remains a genuine Markov kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace NearlyMinimax

def cubeRetraction (d : ℕ) (x : Covariate d) : unitCube d :=
  ⟨fun i => max 0 (min (x i) 1), fun _ =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩⟩

theorem cubeRetraction_continuous (d : ℕ) : Continuous (cubeRetraction d) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => continuous_const.sup ((continuous_apply i).inf continuous_const))

theorem cubeRetraction_measurable (d : ℕ) : Measurable (cubeRetraction d) :=
  (cubeRetraction_continuous d).measurable

theorem cubeRetraction_coe {d : ℕ} (x : unitCube d) : cubeRetraction d x.val = x := by
  apply Subtype.ext
  funext i
  exact (max_eq_right (by simpa only [min_eq_left (x.property i).2] using (x.property i).1)).trans
    (min_eq_left (x.property i).2)

theorem cubeRetraction_val {d : ℕ} (x : Covariate d) (hx : x ∈ unitCube d) :
    (cubeRetraction d x).val = x := by
  exact congrArg Subtype.val (cubeRetraction_coe ⟨x,hx⟩)

structure CubeRegressionParameter (d : ℕ) where
  density : unitCube d → ℝ
  regression : unitCube d → ℝ
  variance : ℝ
  errors : Kernel (unitCube d) ℝ
  errors_markov : IsMarkovKernel errors

attribute [instance] CubeRegressionParameter.errors_markov

def CubeRegressionParameter.toAmbient {d : ℕ} (θ : CubeRegressionParameter d) :
    RegressionParameter d where
  density := θ.density ∘ cubeRetraction d
  regression := θ.regression ∘ cubeRetraction d
  variance := θ.variance
  errors := θ.errors.comap (cubeRetraction d) (cubeRetraction_measurable d)
  errors_markov := inferInstance

def RegressionParameter.onCube {d : ℕ} (θ : RegressionParameter d) :
    CubeRegressionParameter d where
  density := θ.density ∘ Subtype.val
  regression := θ.regression ∘ Subtype.val
  variance := θ.variance
  errors := θ.errors.comap Subtype.val measurable_subtype_coe
  errors_markov := inferInstance

theorem CubeRegressionParameter.toAmbient_density {d : ℕ}
    (θ : CubeRegressionParameter d) (x : unitCube d) : θ.toAmbient.density x = θ.density x := by
  exact congrArg θ.density (cubeRetraction_coe x)

theorem CubeRegressionParameter.toAmbient_regression {d : ℕ}
    (θ : CubeRegressionParameter d) (x : unitCube d) : θ.toAmbient.regression x = θ.regression x := by
  exact congrArg θ.regression (cubeRetraction_coe x)

theorem CubeRegressionParameter.toAmbient_errors {d : ℕ}
    (θ : CubeRegressionParameter d) (x : unitCube d) : θ.toAmbient.errors x = θ.errors x := by
  change θ.errors (cubeRetraction d x.val) = θ.errors x
  rw [cubeRetraction_coe]

theorem cubeRetraction_unitCube_measurableSet (d : ℕ) : MeasurableSet (unitCube d) := by
  have he : unitCube d = Set.univ.pi (fun _ : Fin d => Icc (0 : ℝ) 1) := by
    ext x
    simp only [unitCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_imp_iff, Set.mem_Icc]
  rw [he]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem designLaw_cube_supported {d : ℕ} (θ : RegressionParameter d) :
    ∀ᵐ x ∂designLaw θ, x ∈ unitCube d := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (cubeRetraction_unitCube_measurableSet d))

theorem designLaw_congr_on_cube {d : ℕ} (θ ν : RegressionParameter d)
    (h : ∀ x ∈ unitCube d, θ.density x = ν.density x) : designLaw θ = designLaw ν := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (cubeRetraction_unitCube_measurableSet d)] with x hx
  exact congrArg ENNReal.ofReal (h x hx)

theorem observationLaw_congr_on_cube {d : ℕ} (θ ν : RegressionParameter d)
    (hp : ∀ x ∈ unitCube d, θ.density x = ν.density x)
    (hf : ∀ x ∈ unitCube d, θ.regression x = ν.regression x)
    (hQ : ∀ x ∈ unitCube d, θ.errors x = ν.errors x) :
    observationLaw θ = observationLaw ν := by
  have he : θ.errors =ᵐ[designLaw θ] ν.errors := (designLaw_cube_supported θ).mono hQ
  unfold observationLaw
  rw [← designLaw_congr_on_cube θ ν hp, Measure.compProd_congr he]
  apply Measure.map_congr
  have hc := Measure.ae_compProd_of_ae_fst ν.errors
    (cubeRetraction_unitCube_measurableSet d) (designLaw_cube_supported θ)
  filter_upwards [hc] with z hz
  exact congrArg (fun f => (z.1, f+z.2)) (hf z.1 hz)

theorem RegressionParameter.onCube_toAmbient_observationLaw {d : ℕ}
    (θ : RegressionParameter d) : observationLaw θ.onCube.toAmbient = observationLaw θ := by
  apply observationLaw_congr_on_cube
  · intro x hx
    exact congrArg θ.density (cubeRetraction_val x hx)
  · intro x hx
    exact congrArg θ.regression (cubeRetraction_val x hx)
  · intro x hx
    change θ.errors (cubeRetraction d x).val = θ.errors x
    rw [cubeRetraction_val x hx]

theorem RegressionParameter.onCube_toAmbient_sampleLaw {d : ℕ}
    (θ : RegressionParameter d) (n : ℕ) : sampleLaw θ.onCube.toAmbient n = sampleLaw θ n := by
  unfold sampleLaw
  rw [θ.onCube_toAmbient_observationLaw]

theorem CubeRegressionParameter.toAmbient_measurable {d : ℕ}
    (θ : CubeRegressionParameter d) (hp : Measurable θ.density)
    (hf : Measurable θ.regression) :
    Measurable θ.toAmbient.density ∧ Measurable θ.toAmbient.regression :=
  ⟨hp.comp (cubeRetraction_measurable d), hf.comp (cubeRetraction_measurable d)⟩

theorem RegressionParameter.onCube_toAmbient_admissible {d : ℕ}
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Admissible C θ.onCube.toAmbient := by
  rcases hθ with ⟨hp, hf, hb, hmass, hF, hvlo, hvhi, hQ⟩
  have hpc (x : Covariate d) (hx : x ∈ unitCube d) :
      θ.onCube.toAmbient.density x = θ.density x :=
    congrArg θ.density (cubeRetraction_val x hx)
  have hfc (x : Covariate d) (hx : x ∈ unitCube d) :
      θ.onCube.toAmbient.regression x = θ.regression x :=
    congrArg θ.regression (cubeRetraction_val x hx)
  have hQc (x : Covariate d) (hx : x ∈ unitCube d) :
      θ.onCube.toAmbient.errors x = θ.errors x := by
    change θ.errors (cubeRetraction d x).val = θ.errors x
    rw [cubeRetraction_val x hx]
  have hmem : ∀ᵐ x ∂cubeVolume d, x ∈ unitCube d :=
    ae_restrict_mem (cubeRetraction_unitCube_measurableSet d)
  have hd := designLaw_congr_on_cube θ.onCube.toAmbient θ hpc
  refine ⟨hp.comp ((cubeRetraction_continuous d).subtype_val.measurable),
    hf.comp ((cubeRetraction_continuous d).subtype_val.measurable), ?_, ?_, ?_, hvlo, hvhi, ?_⟩
  · filter_upwards [hb, hmem] with x hx hxc
    rw [hpc x hxc]
    exact hx
  · calc
      _ = ∫⁻ x, ENNReal.ofReal (θ.density x) ∂cubeVolume d := by
        apply lintegral_congr_ae
        exact hmem.mono (fun x hx => congrArg ENNReal.ofReal (hpc x hx))
      _ = 1 := hmass
  · obtain ⟨F, he, hreg, hnorm⟩ := hF
    exact ⟨F, fun x hx => (he x hx).trans (hfc x hx).symm, hreg, hnorm⟩
  · rw [hd]
    filter_upwards [hQ, designLaw_cube_supported θ] with x hx hxc
    rw [hQc x hxc]
    exact hx

theorem RegressionParameter.onCube_toAmbient_meanSquaredRisk {d n : ℕ}
    (θ : RegressionParameter d) (T : Estimator d n) :
    meanSquaredRisk T θ.onCube.toAmbient = meanSquaredRisk T θ := by
  unfold meanSquaredRisk
  rw [θ.onCube_toAmbient_sampleLaw]
  rfl

def cubeWorstCaseRisk {d n : ℕ} (C : ModelConstants d) (T : Estimator d n) : ℝ≥0∞ :=
  ⨆ θ : {θ : CubeRegressionParameter d // Admissible C θ.toAmbient},
    meanSquaredRisk T θ.val.toAmbient

theorem worstCaseRisk_eq_cubeWorstCaseRisk {d n : ℕ}
    (C : ModelConstants d) (T : Estimator d n) : worstCaseRisk C T = cubeWorstCaseRisk C T := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    let χ : {θ : CubeRegressionParameter d // Admissible C θ.toAmbient} :=
      ⟨θ.val.onCube, θ.val.onCube_toAmbient_admissible C θ.property⟩
    calc
      meanSquaredRisk T θ.val = meanSquaredRisk T χ.val.toAmbient :=
        (θ.val.onCube_toAmbient_meanSquaredRisk T).symm
      _ ≤ cubeWorstCaseRisk C T := le_iSup_of_le χ le_rfl
  · apply iSup_le
    intro θ
    exact le_iSup_of_le (⟨θ.val.toAmbient,θ.property⟩ : {θ : RegressionParameter d // Admissible C θ})
      le_rfl

theorem minimaxRisk_eq_cube_parameter_inf {d : ℕ} (C : ModelConstants d) (n : ℕ) :
    minimaxRisk C n = ⨅ T : Estimator d n, cubeWorstCaseRisk C T := by
  unfold minimaxRisk
  apply iInf_congr
  intro T
  exact worstCaseRisk_eq_cubeWorstCaseRisk C T

end NearlyMinimax
