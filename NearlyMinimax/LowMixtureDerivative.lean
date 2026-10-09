module

public import NearlyMinimax.LowSmoothness


@[expose] public section

/-! Differentiation of the actual finite latent experiment after integration
over a finite design measure. Uniform domination is proved from finite polynomial
formulas on a compact box; no bound on the score is assumed. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators
namespace NearlyMinimax

abbrev FiniteExperimentData (m n : ℕ) :=
  ℝ × (((Fin m → Fin 3) → Fin n → ℝ) × ((Fin n → Fin 3) → ℝ))

def finiteExperimentRawDerivative (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, (activationProductPriorDerivative m t ξ *
      (∑ y, finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y * T y) +
    activationProductPrior m t ξ *
      (∑ y, ((∑ i, finiteResponseVarianceTerm m n a (v - η ^ 2 * t) f ξ y i) *
        (-η ^ 2)) * T y))

theorem finite_experiment_raw_hasDerivAt (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ) :
    HasDerivAt (fun u => finiteExperimentExpectation m n a v η u f T)
      (finiteExperimentRawDerivative m n a v η t f T) t := by
  have hV : HasDerivAt (fun u : ℝ => v - η ^ 2 * u) (-η ^ 2) t :=
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2))).congr_deriv (by ring)
  unfold finiteExperimentExpectation finiteExperimentRawDerivative
  apply HasDerivAt.fun_sum
  intro ξ _
  apply (activation_product_prior_hasDerivAt m t ξ).mul
  apply HasDerivAt.fun_sum
  intro y _
  exact ((finite_response_variance_hasDerivAt m n a (v - η ^ 2 * t) f ξ y).comp t hV).mul_const (T y)

theorem ternaryMass_joint_continuous (a : ℝ) (y : Fin 3) :
    Continuous (fun z : ℝ × ℝ => ternaryMass a z.1 z.2 y) := by
  fin_cases y <;> simp [ternaryMass] <;> fun_prop

private theorem finite_response_data_continuous (m n : ℕ) (a v η : ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteResponseLikelihood m n a (v - η ^ 2 * z.1) z.2.1 ξ y) := by
  unfold finiteResponseLikelihood
  apply continuous_finset_prod
  intro i _
  exact (ternaryMass_joint_continuous a (y i)).comp
    ((show Continuous (fun z : FiniteExperimentData m n => z.2.1 ξ i) from by fun_prop).prodMk
      (show Continuous (fun z : FiniteExperimentData m n => v - η ^ 2 * z.1) from by fun_prop))

private theorem finite_variance_data_continuous (m n : ℕ) (a v η : ℝ)
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) (i : Fin n) :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteResponseVarianceTerm m n a (v - η ^ 2 * z.1) z.2.1 ξ y i) := by
  unfold finiteResponseVarianceTerm
  apply Continuous.const_mul
  apply continuous_finset_prod
  intro k _
  exact (ternaryMass_joint_continuous a (y k)).comp
    ((show Continuous (fun z : FiniteExperimentData m n => z.2.1 ξ k) from by fun_prop).prodMk
      (show Continuous (fun z : FiniteExperimentData m n => v - η ^ 2 * z.1) from by fun_prop))

theorem finite_experiment_expectation_data_continuous (m n : ℕ) (a v η : ℝ) :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentExpectation m n a v η z.1 z.2.1 z.2.2) := by
  unfold finiteExperimentExpectation
  apply continuous_finset_sum
  intro ξ _
  apply Continuous.mul
  · exact (continuous_iff_continuousAt.mpr (fun t =>
      (activation_product_prior_hasDerivAt m t ξ).continuousAt)).comp continuous_fst
  · apply continuous_finset_sum
    intro y _
    exact (finite_response_data_continuous m n a v η ξ y).mul
      ((continuous_apply y).comp (continuous_snd.comp continuous_snd))

theorem finite_experiment_raw_derivative_data_continuous (m n : ℕ) (a v η : ℝ) :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentRawDerivative m n a v η z.1 z.2.1 z.2.2) := by
  unfold finiteExperimentRawDerivative
  apply continuous_finset_sum
  intro ξ _
  apply Continuous.add
  · apply Continuous.mul
    · unfold activationProductPriorDerivative
      apply continuous_finset_sum
      intro j _
      apply Continuous.const_mul
      apply continuous_finset_prod
      intro k _
      exact (continuous_iff_continuousAt.mpr (fun t =>
        (activation_prior_hasDerivAt t (ξ k)).continuousAt)).comp continuous_fst
    · apply continuous_finset_sum
      intro y _
      exact (finite_response_data_continuous m n a v η ξ y).mul
        ((continuous_apply y).comp (continuous_snd.comp continuous_snd))
  · apply Continuous.mul
    · exact (continuous_iff_continuousAt.mpr (fun t =>
        (activation_product_prior_hasDerivAt m t ξ).continuousAt)).comp continuous_fst
    · apply continuous_finset_sum
      intro y _
      apply Continuous.mul
      · apply Continuous.mul_const
        apply continuous_finset_sum
        intro i _
        exact finite_variance_data_continuous m n a v η ξ y i
      · exact (continuous_apply y).comp (continuous_snd.comp continuous_snd)

/-- Both the expectation and its raw derivative are bounded on each finite
parameter box, including parameter values outside the probability interval. -/
theorem finite_experiment_uniform_box_bound (m n : ℕ) (a v η R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t : ℝ)
      (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ),
      |t| ≤ R → ‖f‖ ≤ R → ‖T‖ ≤ R →
      ‖finiteExperimentExpectation m n a v η t f T‖ ≤ B ∧
      ‖finiteExperimentRawDerivative m n a v η t f T‖ ≤ B := by
  let G : FiniteExperimentData m n → ℝ × ℝ := fun z =>
    (finiteExperimentExpectation m n a v η z.1 z.2.1 z.2.2,
      finiteExperimentRawDerivative m n a v η z.1 z.2.1 z.2.2)
  have hG : Continuous G := (finite_experiment_expectation_data_continuous m n a v η).prodMk
    (finite_experiment_raw_derivative_data_continuous m n a v η)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FiniteExperimentData m n) R).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max 1 C, (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _), ?_⟩
  intro t f T ht hf hT
  have hz : (t, (f, T)) ∈ closedBall (0 : FiniteExperimentData m n) R := by
    rw [mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.mpr ⟨by simpa only [Real.norm_eq_abs] using ht,
      norm_prod_le_iff.mpr ⟨hf, hT⟩⟩
  exact norm_prod_le_iff.mp ((hC _ hz).trans (le_max_right _ _))

section Integrated
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

set_option maxHeartbeats 200000 in
/-- Bounded measurable fields and data observables can be differentiated after
integration over the actual design law. The domination needed for interchange
is derived from the finite polynomial formulas. -/
theorem finite_experiment_integrated_raw_hasDerivAt (m n : ℕ) (a v η t ρ M : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (T : α → (Fin n → Fin 3) → ℝ)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M) :
    Integrable (fun x => finiteExperimentRawDerivative m n a v η t (f x) (T x)) μ ∧
      HasDerivAt (fun u => ∫ x, finiteExperimentExpectation m n a v η u (f x) (T x) ∂μ)
        (∫ x, finiteExperimentRawDerivative m n a v η t (f x) (T x) ∂μ) t := by
  let R := max (|t| + 1) (max ρ M)
  obtain ⟨B, hB, hBox⟩ := finite_experiment_uniform_box_bound m n a v η R
  let F : ℝ → α → ℝ := fun u x => finiteExperimentExpectation m n a v η u (f x) (T x)
  let D : ℝ → α → ℝ := fun u x => finiteExperimentRawDerivative m n a v η u (f x) (T x)
  have hData (u : ℝ) : Measurable (fun x : α => (u, (f x, T x))) :=
    measurable_const.prodMk (hf.prodMk hT)
  have hFData : Measurable (fun z : FiniteExperimentData m n =>
      finiteExperimentExpectation m n a v η z.1 z.2.1 z.2.2) :=
    (finite_experiment_expectation_data_continuous m n a v η).measurable
  have hDData : Measurable (fun z : FiniteExperimentData m n =>
      finiteExperimentRawDerivative m n a v η z.1 z.2.1 z.2.2) :=
    (finite_experiment_raw_derivative_data_continuous m n a v η).measurable
  have hFmeas (u : ℝ) : Measurable (F u) := by
    have hComp := hFData.comp (hData u)
    exact hComp
  have hDmeas (u : ℝ) : Measurable (D u) := by
    have hComp := hDData.comp (hData u)
    exact hComp
  have hFields : ∀ᵐ x ∂μ, ‖f x‖ ≤ R ∧ ‖T x‖ ≤ R := by
    filter_upwards [hfBound, hTBound] with x hfx hTx
    exact ⟨hfx.trans ((le_max_left ρ M).trans (le_max_right _ _)),
      hTx.trans ((le_max_right ρ M).trans (le_max_right _ _))⟩
  have htR : |t| ≤ R := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (le_max_left _ _)
  have hFint : Integrable (F t) μ := Integrable.of_bound (hFmeas t).aestronglyMeasurable B (by
    filter_upwards [hFields] with x hx
    exact (hBox t (f x) (T x) htR hx.1 hx.2).1)
  have hDom : ∀ᵐ x ∂μ, ∀ u ∈ ball t 1, ‖D u x‖ ≤ B := by
    filter_upwards [hFields] with x hx
    intro u hu
    have hut : ‖u - t‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hu
    have huR : |u| ≤ R := by
      have huNorm : ‖u‖ ≤ |t| + 1 := calc
        ‖u‖ ≤ ‖u - t‖ + ‖t‖ := norm_le_norm_sub_add u t
        _ ≤ 1 + ‖t‖ := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      have huAbs : |u| ≤ |t| + 1 := by simpa only [Real.norm_eq_abs] using huNorm
      exact huAbs.trans (le_max_left _ _)
    exact (hBox u (f x) (T x) huR hx.1 hx.2).2
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := D) (bound := fun _ => B) (s := ball t 1)
    (ball_mem_nhds t (by norm_num))
    (Filter.Eventually.of_forall (fun u => (hFmeas u).aestronglyMeasurable)) hFint
    (hDmeas t).aestronglyMeasurable hDom (integrable_const B)
    (Filter.Eventually.of_forall (fun x u _ => finite_experiment_raw_hasDerivAt m n a v η u (f x) (T x)))

theorem finite_experiment_raw_derivative_eq_score (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ)
    (hpositive : ∀ ξ y, 0 < finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y) :
    finiteExperimentRawDerivative m n a v η t f T =
      ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y *
          T y * finiteExperimentScore m n a (v - η ^ 2 * t) η f ξ y :=
  (finite_experiment_raw_hasDerivAt m n a v η t f T).unique
    (finite_experiment_observable_score_hasDerivAt m n a v η t f T hpositive)

/-- The integrated derivative is continuous, so its interval integrability
on a bounded parameter path is a consequence of the actual finite formulas. -/
theorem finite_experiment_integrated_raw_derivative_continuous (m n : ℕ) (a v η ρ M : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (T : α → (Fin n → Fin 3) → ℝ)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M) :
    Continuous (fun t => ∫ x, finiteExperimentRawDerivative m n a v η t (f x) (T x) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let R := max (|t| + 1) (max ρ M)
  obtain ⟨B, hB, hBox⟩ := finite_experiment_uniform_box_bound m n a v η R
  let D : ℝ → α → ℝ := fun u x => finiteExperimentRawDerivative m n a v η u (f x) (T x)
  have hData (u : ℝ) : Measurable (fun x : α => (u, (f x, T x))) :=
    measurable_const.prodMk (hf.prodMk hT)
  have hDData : Measurable (fun z : FiniteExperimentData m n =>
      finiteExperimentRawDerivative m n a v η z.1 z.2.1 z.2.2) :=
    (finite_experiment_raw_derivative_data_continuous m n a v η).measurable
  have hDmeas (u : ℝ) : Measurable (D u) := by
    have hComp := hDData.comp (hData u)
    exact hComp
  have hDom : ∀ᶠ u in 𝓝 t, ∀ᵐ x ∂μ, ‖D u x‖ ≤ B := by
    filter_upwards [ball_mem_nhds t (by norm_num : (0 : ℝ) < 1)] with u hu
    filter_upwards [hfBound, hTBound] with x hfx hTx
    have hut : ‖u - t‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hu
    have huR : |u| ≤ R := by
      have huNorm : ‖u‖ ≤ |t| + 1 := calc
        ‖u‖ ≤ ‖u - t‖ + ‖t‖ := norm_le_norm_sub_add u t
        _ ≤ 1 + ‖t‖ := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      have huAbs : |u| ≤ |t| + 1 := by simpa only [Real.norm_eq_abs] using huNorm
      exact huAbs.trans (le_max_left _ _)
    exact (hBox u (f x) (T x) huR
      (hfx.trans ((le_max_left ρ M).trans (le_max_right _ _)))
      (hTx.trans ((le_max_right ρ M).trans (le_max_right _ _)))).2
  have hCont : ∀ᵐ x ∂μ, ContinuousAt (fun u => D u x) t := by
    apply Filter.Eventually.of_forall
    intro x
    have hDataCont : Continuous (fun u : ℝ => (u, (f x, T x))) :=
      continuous_id.prodMk continuous_const
    have hComp := (finite_experiment_raw_derivative_data_continuous m n a v η).comp hDataCont
    exact hComp.continuousAt
  exact continuousAt_of_dominated (F := D) (bound := fun _ => B)
    (Filter.Eventually.of_forall (fun u => (hDmeas u).aestronglyMeasurable)) hDom (integrable_const B) hCont

/-- Exact score representation after integrating over the design. Likelihood
positivity is needed only at the differentiation point. -/
theorem finite_experiment_integrated_score_hasDerivAt (m n : ℕ) (a v η t ρ M : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (T : α → (Fin n → Fin 3) → ℝ)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M)
    (hpositive : ∀ᵐ x ∂μ, ∀ ξ y,
      0 < finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y) :
    let S := fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
      finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y *
        T x y * finiteExperimentScore m n a (v - η ^ 2 * t) η (f x) ξ y
    Integrable S μ ∧ HasDerivAt
      (fun u => ∫ x, finiteExperimentExpectation m n a v η u (f x) (T x) ∂μ)
      (∫ x, S x ∂μ) t := by
  dsimp only
  obtain ⟨hInt, hDeriv⟩ := finite_experiment_integrated_raw_hasDerivAt μ m n a v η t ρ M f T hf hT hfBound hTBound
  have he : (fun x => finiteExperimentRawDerivative m n a v η t (f x) (T x)) =ᵐ[μ]
      (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y *
          T x y * finiteExperimentScore m n a (v - η ^ 2 * t) η (f x) ξ y) := by
    filter_upwards [hpositive] with x hx
    exact finite_experiment_raw_derivative_eq_score m n a v η t (f x) (T x) hx
  exact ⟨hInt.congr he, (integral_congr_ae he) ▸ hDeriv⟩

end Integrated
end NearlyMinimax
