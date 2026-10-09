module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ObservationMoments


@[expose] public section

/-! Two-observation Bochner disintegration on the actual observation law. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem observationPair_integral_conditioning {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : Observation d × Observation d → ℝ)
    (hg : Integrable g ((observationLaw θ).prod (observationLaw θ))) :
    (∫ z, g z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x : Covariate d × Covariate d,
        ∫ u : ℝ × ℝ, g ((x.1, θ.regression x.1 + u.1),
          (x.2, θ.regression x.2 + u.2)) ∂(θ.errors x.1).prod (θ.errors x.2)
        ∂(designLaw θ).prod (designLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  let := designLaw_isProbability C θ hθ
  have ho := measurePreserving_finTwoArrow (observationLaw θ)
  have hd := measurePreserving_finTwoArrow (designLaw θ)
  have hi : Integrable (fun z : Fin 2 → Observation d => g (z 0, z 1)) (sampleLaw θ 2) :=
    ho.integrable_comp_of_integrable hg
  have hs := sampleLaw_integral_conditioning C θ hθ _ hi
  have he : ∀ x : Fin 2 → Covariate d,
      (∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1))
        ∂conditionalErrorLaw θ x) =
      ∫ u : ℝ × ℝ, g ((x 0, θ.regression (x 0) + u.1),
        (x 1, θ.regression (x 1) + u.2)) ∂(θ.errors (x 0)).prod (θ.errors (x 1)) := by
    intro x
    have h := (measurePreserving_piFinTwo (fun i : Fin 2 => θ.errors (x i))).integral_comp'
      (fun u : ℝ × ℝ => g ((x 0, θ.regression (x 0) + u.1),
        (x 1, θ.regression (x 1) + u.2)))
    exact h
  calc
    _ = ∫ z : Fin 2 → Observation d, g (z 0, z 1) ∂sampleLaw θ 2 :=
      (ho.integral_comp' g).symm
    _ = ∫ x : Fin 2 → Covariate d,
        ∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1))
          ∂conditionalErrorLaw θ x ∂designVectorLaw θ 2 := hs
    _ = ∫ x : Fin 2 → Covariate d,
        ∫ u : ℝ × ℝ, g ((x 0, θ.regression (x 0) + u.1),
          (x 1, θ.regression (x 1) + u.2)) ∂(θ.errors (x 0)).prod (θ.errors (x 1))
        ∂designVectorLaw θ 2 := by simp_rw [he]
    _ = _ := hd.integral_comp' (fun x : Covariate d × Covariate d =>
      ∫ u : ℝ × ℝ, g ((x.1, θ.regression x.1 + u.1),
        (x.2, θ.regression x.2 + u.2)) ∂(θ.errors x.1).prod (θ.errors x.2))

end NearlyMinimax
