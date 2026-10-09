module

public import NearlyMinimax.HighRawObservable


@[expose] public section

/-! Genuine variance-path derivatives of bounded raw data observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Differentiating the real bounded data observable follows from the actual
finite ternary product derivative and a derived constant majorant. -/
theorem highRawObservable_hasDerivAt_path {d : ℕ} (n : ℕ) (a v η t T P B : ℝ)
    (ha : 0 < a) (ht : 0 < t) (htT : t < T) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Ioo 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) (ω : Ω) :
    HasDerivAt (fun u => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H)
      (-η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H) t := by
  let L : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z
  let L' : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * (-η ^ 2 *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)
  have hLM (u : ℝ) : Measurable (L u) := by
    have hj : Measurable (Function.uncurry (fun ω z =>
        highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z)) :=
      highRawSampleLikelihood_joint_measurable n a (v - η ^ 2 * u) p F hp hF
    have hw : Measurable (fun z => highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z) :=
      hj.of_uncurry_left
    exact (hH.comp (encodeDesignResponse_measurable a)).mul hw
  have hL'M (u : ℝ) : Measurable (L' u) := by
    have hj : Measurable (Function.uncurry (fun ω z =>
        highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)) :=
      highRawSampleVarianceDerivative_joint_measurable n a (v - η ^ 2 * u) p F hp hF
    have hw : Measurable (fun z => highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z) :=
      hj.of_uncurry_left
    exact (hH.comp (encodeDesignResponse_measurable a)).mul (hw.const_mul (-η ^ 2))
  have hi : Integrable (L t) (highSampleReference d n) := by
    apply Integrable.of_bound (hLM t).aestronglyMeasurable (B * P ^ n)
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * t) (p ω) (F ω) z‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a (v - η ^ 2 * t) P
        hP (p ω) (F ω) (hpb ω) ha.ne' (hq t ⟨ht, htT⟩ ω) z) (abs_nonneg _) hB
  have hb (u : ℝ) (hu : u ∈ Ioo 0 T) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
      ‖L' u z‖ ≤ B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2))) := by
    change ‖H (encodeDesignResponse a z) * (-η ^ 2 *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul (hHb _) (mul_le_mul_of_nonneg_left
      (highRawSampleVarianceDerivative_abs_le n a (v - η ^ 2 * u) P ha hP
        (p ω) (F ω) (hpb ω) (hq u hu ω) z) (sq_nonneg η)) (by positivity) hB
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := highSampleReference d n) (F := L) (F' := L')
    (bound := fun _ => B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2))))
    (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
    (Eventually.of_forall fun u => (hLM u).aestronglyMeasurable) hi
    (hL'M t).aestronglyMeasurable
    (Eventually.of_forall fun z u hu => hb u hu z)
    (integrable_const _)
    (Eventually.of_forall fun z u _ =>
      (highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z).const_mul
        (H (encodeDesignResponse a z)))).2
  change HasDerivAt (fun u => ∫ z, L u z ∂highSampleReference d n) _ t
  apply hd.congr_deriv
  change (∫ z, L' t z ∂highSampleReference d n) =
    -η ^ 2 * ∫ z, H (encodeDesignResponse a z) *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) z ∂highSampleReference d n
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by dsimp [L']; ring

end NearlyMinimax
