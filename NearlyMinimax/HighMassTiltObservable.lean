module

public import NearlyMinimax.HighMassTilt


@[expose] public section

/-! Exact observable cancellation for genuine mass-tilted high-prior experiments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual tilted-prior/data integration cancels m^n against the true sample density.
This identity holds for arbitrary real observables, with the usual total Bochner integral. -/
theorem massPowerTilt_highSample_integral {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ) :
    (∫ z, H z ∂(massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V p F hp hF)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z, highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * H z
          ∂ν.prod (highSampleReference d n) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hbound
  have hu0 (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) :
      0 ≤ highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 (z.2.1 i)).1)
      (hq z.1 (z.2.1 i) (z.2.2 i)))
  have hD : Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      ENNReal.ofReal (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 /
        massPowerNormalizer ν m n)) :=
    ENNReal.measurable_ofReal.comp ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).div_const _)
  rw [massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw,
    integral_withDensity_eq_integral_toReal_smul hD
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hu0 _) hG.le), smul_eq_mul]
  calc
    _ = ∫ z, (massPowerNormalizer ν m n)⁻¹ *
        (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * H z)
          ∂ν.prod (highSampleReference d n) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by ring
    _ = _ := integral_const_mul _ _

end NearlyMinimax
