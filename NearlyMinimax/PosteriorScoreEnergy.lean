module

public import NearlyMinimax.WeightedScoreContraction


@[expose] public section

/-! Actual posterior score L2 and Fisher contraction under marginalization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

def posteriorMeanScore (ν : Measure Ω) (L D : Ω × Z → ℝ) (z : Z) : ℝ :=
  (∫ ω, D (ω,z) ∂ν) / (∫ ω, L (ω,z) ∂ν)

theorem posteriorMeanScore_measurable (ν : Measure Ω) [SFinite ν]
    (L D : Ω × Z → ℝ) (hL : Measurable L) (hD : Measurable D) :
    Measurable (posteriorMeanScore ν L D) :=
  hD.stronglyMeasurable.integral_prod_left'.measurable.div
    hL.stronglyMeasurable.integral_prod_left'.measurable

/-- Genuine marginal Fisher energy contracts the true latent Fisher
energy. The premises are primitive likelihood/derivative integrability. -/
theorem posteriorMeanScore_memLp_energy (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Measure Z) [SFinite μ] (L D : Ω × Z → ℝ)
    (hLm : Measurable L) (hDm : Measurable D) (hLp : ∀ z, 0 < L z)
    (LC DC G : ℝ) (hG : 0 < G) (hLb : ∀ z, L z ≤ LC) (hDb : ∀ z, |D z| ≤ DC)
    (hE : Integrable (fun z => D z^2 / L z) (ν.prod μ)) :
    let ρ := μ.withDensity (fun z => ENNReal.ofReal ((∫ ω, L (ω,z) ∂ν) / G))
    MemLp (posteriorMeanScore ν L D) 2 ρ ∧
      (∫ z, (posteriorMeanScore ν L D z)^2 ∂ρ) ≤
        G⁻¹ * ∫ z, D z^2 / L z ∂ν.prod μ := by
  let M : Z → ℝ := fun z => ∫ ω, L (ω,z) ∂ν
  let A : Z → ℝ := fun z => ∫ ω, D (ω,z) ∂ν
  let E : Z → ℝ := fun z => ∫ ω, D (ω,z)^2 / L (ω,z) ∂ν
  let R : Z → ℝ := posteriorMeanScore ν L D
  let ρ := μ.withDensity (fun z => ENNReal.ofReal (M z / G))
  have hM : Measurable M := hLm.stronglyMeasurable.integral_prod_left'.measurable
  have hA : Measurable A := hDm.stronglyMeasurable.integral_prod_left'.measurable
  have hR : Measurable R := posteriorMeanScore_measurable ν L D hLm hDm
  have hden (z) : 0 < M z := integral_likelihood_pos ν _
    (hLm.comp (measurable_id.prodMk measurable_const)) LC
    (fun ω => hLp (ω,z)) (fun ω => hLb (ω,z))
  have hiL (z) : Integrable (fun ω => L (ω,z)) ν := by
    apply Integrable.of_bound (hLm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable LC
    exact Eventually.of_forall fun ω => by
      change ‖L (ω,z)‖ ≤ LC
      rw [Real.norm_eq_abs, abs_of_nonneg (hLp _).le]
      exact hLb _
  have hiD (z) : Integrable (fun ω => D (ω,z)) ν := by
    apply Integrable.of_bound (hDm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable DC
    exact Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using hDb (ω,z)
  have hE0 (z) : 0 ≤ E z := integral_nonneg (fun ω => div_nonneg (sq_nonneg _) (hLp _).le)
  have hEnergy : ∀ᵐ z ∂μ, (M z / G) * R z^2 ≤ G⁻¹ * E z := by
    filter_upwards [hE.prod_left_ae] with z hEz
    have hc := weighted_score_energy_contraction ν (fun ω => L (ω,z)) (fun ω => D (ω,z))
      (fun ω => hLp (ω,z)) (hiL z) (hiD z) hEz (hden z)
    have halg : (M z / G) * R z^2 = G⁻¹ * (A z^2 / M z) := by
      dsimp only [R, posteriorMeanScore, A, M]
      field_simp [(hden z).ne',hG.ne'] <;> ring
    rw [halg]
    exact mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hG.le)
  have hiE : Integrable (fun z => G⁻¹ * E z) μ := hE.integral_prod_right.const_mul _
  have hweighted : Integrable (fun z => (M z/G) * R z^2) μ := by
    apply hiE.mono' ((hM.div_const _).mul (hR.pow_const 2)).aestronglyMeasurable
    filter_upwards [hEnergy] with z hz
    change ‖(M z/G) * R z^2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (hden z).le hG.le) (sq_nonneg _))]
    exact hz
  have hdens : Measurable (fun z => ENNReal.ofReal (M z/G)) := (hM.div_const G).ennreal_ofReal
  have hsquare : Integrable (fun z => R z^2) ρ := by
    apply (integrable_withDensity_iff_integrable_smul' hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
    simpa only [ENNReal.toReal_ofReal (div_nonneg (hden _).le hG.le), smul_eq_mul] using hweighted
  refine ⟨(memLp_two_iff_integrable_sq hR.aestronglyMeasurable).2 hsquare, ?_⟩
  change (∫ z, R z^2 ∂ρ) ≤ _
  rw [integral_withDensity_eq_integral_toReal_smul hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hden _).le hG.le), smul_eq_mul]
  calc
    _ ≤ ∫ z, G⁻¹ * E z ∂μ := integral_mono_ae hweighted hiE hEnergy
    _ = _ := by rw [integral_const_mul, ← MeasureTheory.integral_prod_symm _ hE]

end NearlyMinimax
