module

public import NearlyMinimax.GaussianSeparatedCharacteristic


@[expose] public section

/-! Exact absolute first moments of actual standard Gaussian projections. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def gaussianAbsoluteMean : ℝ := ∫ z : ℝ, |z| ∂standardGaussianLine

theorem standardGaussianLine_abs_integrable :
    Integrable (fun z : ℝ => |z|) standardGaussianLine := by
  simpa only [Real.norm_eq_abs, id_eq] using
    (IsGaussian.integrable_id (μ := standardGaussianLine)).norm

theorem gaussianAbsoluteMean_pos : 0 < gaussianAbsoluteMean := by
  have hn : 0 ≤ gaussianAbsoluteMean := integral_nonneg (fun _ => abs_nonneg _)
  by_contra h
  have hz : gaussianAbsoluteMean = 0 := le_antisymm (not_lt.mp h) hn
  have habs : (fun z : ℝ => |z|) =ᵐ[standardGaussianLine] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg z) standardGaussianLine_abs_integrable).mp hz
  have hid : id =ᵐ[standardGaussianLine] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [habs] with z hz
    exact abs_eq_zero.mp hz
  have hv := variance_congr hid
  rw [variance_id_gaussianReal] at hv
  change (1 : ℝ) = Var[(0 : ℝ → ℝ); standardGaussianLine] at hv
  rw [variance_zero] at hv
  exact one_ne_zero hv

theorem euclideanNorm_eq_toLp_norm {d : ℕ} (v : Covariate d) :
    euclideanNorm v = ‖WithLp.toLp 2 v‖ := by
  simp only [euclideanNorm, EuclideanSpace.norm_eq, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]

theorem standardGaussianPi_toLp_measurePreserving (d : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : Covariate d → EuclideanSpace ℝ (Fin d))
      (standardGaussianPi d) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  ⟨by fun_prop, map_pi_eq_stdGaussian⟩

theorem gaussianPhase_eq_inner {d : ℕ} (v Z : Covariate d) :
    gaussianPhase v Z = inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 Z) := by
  simp only [gaussianPhase, PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply,
    conj_trivial, mul_comm]

theorem gaussianPhase_map_eq_scaled_gaussian {d : ℕ} (v : Covariate d) :
    (standardGaussianPi d).map (gaussianPhase v) =
      standardGaussianLine.map (fun z : ℝ => euclideanNorm v * z) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ (WithLp.toLp 2 v)
  have hfun : gaussianPhase v = L ∘ (WithLp.toLp 2) := by
    funext Z
    exact gaussianPhase_eq_inner v Z
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal L,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian, gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  simp only [L, innerSL_apply_norm, ← euclideanNorm_eq_toLp_norm]
  rfl

theorem gaussianPhase_abs_integrable {d : ℕ} (v : Covariate d) :
    Integrable (fun Z => |gaussianPhase v Z|) (standardGaussianPi d) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ (WithLp.toLp 2 v)
  have hi : Integrable (fun X : EuclideanSpace ℝ (Fin d) => |L X|)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa only [Real.norm_eq_abs] using
      (IsGaussian.integrable_dual (stdGaussian (EuclideanSpace ℝ (Fin d))) L).norm
  have hh := (standardGaussianPi_toLp_measurePreserving d).integrable_comp_of_integrable hi
  simpa only [Function.comp_def, L, innerSL_apply_apply, ← gaussianPhase_eq_inner] using hh

theorem gaussianPhase_abs_integral {d : ℕ} (v : Covariate d) :
    (∫ Z, |gaussianPhase v Z| ∂standardGaussianPi d) =
      gaussianAbsoluteMean * euclideanNorm v := by
  have hphase : Measurable (gaussianPhase v) := by unfold gaussianPhase; fun_prop
  have habs : AEStronglyMeasurable (fun z : ℝ => |z|)
      ((standardGaussianPi d).map (gaussianPhase v)) := (by fun_prop : Measurable (fun z : ℝ => |z|)).aestronglyMeasurable
  rw [← integral_map hphase.aemeasurable habs, gaussianPhase_map_eq_scaled_gaussian v,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (show 0 ≤ euclideanNorm v by unfold euclideanNorm; positivity)]
  rw [integral_const_mul]
  exact mul_comm _ _

theorem gaussianPhase_abs_integral_spatial_distance {d : ℕ} (v : Covariate d) :
    (∫ Z, |gaussianPhase v Z| ∂standardGaussianPi d) =
      gaussianAbsoluteMean * Real.sqrt (spatialSquaredDistance 0 v) := by
  simpa only [spatialSquaredDistance, Pi.zero_apply, sub_zero, euclideanNorm] using
    gaussianPhase_abs_integral v

theorem standardGaussianPi_euclideanNorm_integrable (d : ℕ) :
    Integrable (euclideanNorm : Covariate d → ℝ) (standardGaussianPi d) := by
  have hi : Integrable (fun X : EuclideanSpace ℝ (Fin d) => ‖X‖)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa only [id_eq] using (IsGaussian.integrable_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).norm
  simpa only [Function.comp_def, ← euclideanNorm_eq_toLp_norm] using
    (standardGaussianPi_toLp_measurePreserving d).integrable_comp_of_integrable hi

theorem standardGaussianPi_coordinate_abs_integrable (d : ℕ) (i : Fin d) :
    Integrable (fun Z : Covariate d => |Z i|) (standardGaussianPi d) :=
  integrable_comp_eval (μ := fun _ : Fin d => standardGaussianLine) (i := i)
    standardGaussianLine_abs_integrable

theorem standardGaussianPi_coordinate_abs_integral (d : ℕ) (i : Fin d) :
    (∫ Z : Covariate d, |Z i| ∂standardGaussianPi d) = gaussianAbsoluteMean := by
  exact integral_comp_eval (μ := fun _ : Fin d => standardGaussianLine) (i := i)
    standardGaussianLine_abs_integrable.aestronglyMeasurable

theorem standardGaussianPi_l1_integrable (d : ℕ) :
    Integrable (fun Z : Covariate d => ∑ r, |Z r|) (standardGaussianPi d) :=
  integrable_finsetSum _ (fun r _ => standardGaussianPi_coordinate_abs_integrable d r)

theorem standardGaussianPi_l1_integral (d : ℕ) :
    (∫ Z : Covariate d, ∑ r, |Z r| ∂standardGaussianPi d) =
      (d : ℝ) * gaussianAbsoluteMean := by
  rw [integral_finsetSum Finset.univ (fun r _ => standardGaussianPi_coordinate_abs_integrable d r)]
  simp only [standardGaussianPi_coordinate_abs_integral, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end NearlyMinimax
