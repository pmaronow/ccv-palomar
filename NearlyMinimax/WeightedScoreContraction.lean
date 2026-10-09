module

public import NearlyMinimax.MarginalLikelihood


@[expose] public section

/-! Genuine posterior Fisher-energy contraction, proved by expanding a
nonnegative weighted square. -/
noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A marginal likelihood derivative has no more Fisher energy than
its genuine latent likelihood derivative. -/
theorem weighted_score_energy_contraction (ν : Measure Ω) (L D : Ω → ℝ)
    (hL : ∀ ω, 0 < L ω) (hiL : Integrable L ν) (hiD : Integrable D ν)
    (hiE : Integrable (fun ω => D ω ^ 2 / L ω) ν)
    (hmean : 0 < ∫ ω, L ω ∂ν) :
    (∫ ω, D ω ∂ν)^2 / (∫ ω, L ω ∂ν) ≤ ∫ ω, D ω ^ 2 / L ω ∂ν := by
  let r : ℝ := (∫ ω, D ω ∂ν) / (∫ ω, L ω ∂ν)
  have he (ω : Ω) : (D ω - r * L ω)^2 / L ω =
      D ω^2 / L ω - 2*r*D ω + r^2*L ω := by
    field_simp [(hL ω).ne']
    ring
  have hn : 0 ≤ ∫ ω, (D ω - r * L ω)^2 / L ω ∂ν :=
    integral_nonneg (fun ω => div_nonneg (sq_nonneg _) (hL ω).le)
  have hv : (∫ ω, (D ω - r * L ω)^2 / L ω ∂ν) =
      (∫ ω, D ω^2 / L ω ∂ν) - 2*r*(∫ ω, D ω ∂ν) + r^2*(∫ ω, L ω ∂ν) := by
    simp_rw [he]
    have hv1 := integral_add (hiE.sub (hiD.const_mul (2*r))) (hiL.const_mul (r^2))
    rw [integral_sub' hiE (hiD.const_mul (2*r)), integral_const_mul, integral_const_mul] at hv1
    simpa only [Pi.sub_apply] using hv1
  rw [hv] at hn
  have hr : -2*r*(∫ ω, D ω ∂ν) + r^2*(∫ ω, L ω ∂ν) =
      -(∫ ω, D ω ∂ν)^2 / (∫ ω, L ω ∂ν) := by
    dsimp only [r]
    field_simp [hmean.ne']
    ring
  rw [neg_div] at hr
  nlinarith [hn, hr]

end NearlyMinimax
