module

public import NearlyMinimax.HighMassTiltObservable
public import NearlyMinimax.HighObservableProductRule
public import NearlyMinimax.LowSmoothnessVariance


@[expose] public section

/-! Actual raw ternary likelihood derivatives for the high-prior observable product rule. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def highRawSampleVarianceDerivative {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∏ i, p (z.1 i)) * ∑ i, (∏ j ∈ Finset.univ.erase i,
    ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)

theorem highRawSampleLikelihood_hasDerivAt_variance {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    HasDerivAt (fun W => highRawSampleLikelihood n a W p F z)
      (highRawSampleVarianceDerivative n a V p F z) V := by
  have h := (HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => ternary_hasDerivAt_variance a (F (z.1 i)) V (z.2 i))).const_mul
      (∏ i, p (z.1 i))
  simpa only [highRawSampleLikelihood, highRawSampleVarianceDerivative,
    Finset.prod_mul_distrib, smul_eq_mul] using h

theorem highRawSampleLikelihood_hasDerivAt_path {d : ℕ} (n : ℕ) (a v η t : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    HasDerivAt (fun u => highRawSampleLikelihood n a (v - η ^ 2 * u) p F z)
      (-η ^ 2 * highRawSampleVarianceDerivative n a (v - η ^ 2 * t) p F z) t := by
  have h := (highRawSampleLikelihood_hasDerivAt_variance n a (v - η ^ 2 * t) p F z).comp t
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2)))
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_one, mul_comm] using h

theorem highRawSampleLikelihood_abs_le {d : ℕ} (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highRawSampleLikelihood n a V p F z| ≤ P ^ n := by
  unfold highRawSampleLikelihood
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin n, P := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i _
      rw [abs_mul, abs_of_nonneg (hq (z.1 i) (z.2 i))]
      calc
        |p (z.1 i)| * ternaryMass a (F (z.1 i)) V (z.2 i) ≤ P * 1 :=
          mul_le_mul (hp _) (ternary_mass_le_one a _ V ha (hq _) _) (hq _ _) hP
        _ = P := mul_one _
    _ = _ := by simp

theorem highRawSampleVarianceDerivative_abs_le {d : ℕ} (n : ℕ) (a V P : ℝ)
    (ha : 0 < a) (hP : 0 ≤ P) (p F : Covariate d → ℝ)
    (hp : ∀ x, |p x| ≤ P) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highRawSampleVarianceDerivative n a V p F z| ≤ P ^ n * ((n : ℝ) / a ^ 2) := by
  have hpp : |∏ i : Fin n, p (z.1 i)| ≤ P ^ n := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => abs_nonneg (p (z.1 i)))
      (fun i (_ : i ∈ Finset.univ) => hp (z.1 i))
  have hqprod (i : Fin n) :
      |∏ j ∈ Finset.univ.erase i, ternaryMass a (F (z.1 j)) V (z.2 j)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => by
      rw [abs_of_nonneg (hq (z.1 j) (z.2 j))]
      exact ternary_mass_le_one a _ V ha.ne' (hq _) _)
  have hs : |∑ i : Fin n, (∏ j ∈ Finset.univ.erase i,
      ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)| ≤
        (n : ℝ) / a ^ 2 := by
    calc
      _ ≤ ∑ i : Fin n, |(∏ j ∈ Finset.univ.erase i,
          ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact (mul_le_mul (hqprod i) (ternary_variance_derivative_abs_bound a ha (z.2 i))
          (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  rw [highRawSampleVarianceDerivative, abs_mul]
  exact mul_le_mul hpp hs (abs_nonneg _) (pow_nonneg hP n)

theorem highRawSampleVarianceDerivative_joint_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2) := by
  have hx (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact (Finset.measurable_prod _ (fun i _ => hp.comp (hx i))).mul
    (Finset.measurable_sum _ (fun i _ =>
      (Finset.measurable_prod _ (fun j _ =>
        (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx j).prodMk (hy j)))).mul
      ((measurable_of_countable (ternaryVarianceDerivative a)).comp (hy i))))

end NearlyMinimax
