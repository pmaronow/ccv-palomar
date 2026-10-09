module

public import NearlyMinimax.AnchoredFit


@[expose] public section

/-! Population projection error derived from the actual normal equations. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem anchoredVectorMoment_integrable {d ℓ : ℕ} (u : Covariate d)
    (p g : Covariate d → ℝ) (hpmeas : Measurable p) (b : ℝ)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (γ : AnchoredIndex d ℓ) :
    Integrable (fun w => p w * anchoredFeature u w γ * g w) (cubeVolume d) := by
  have hc : ContinuousOn (fun w => anchoredFeature u w γ * g w) (unitCube d) :=
    (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).continuousOn).mul hg
  have hi := ContinuousOn.integrableOn_compact (μ := volume) (unitCube_isCompact d) hc
  have hpi := hi.bdd_mul hpmeas.aestronglyMeasurable
    (hp.mono (fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2))
  convert hpi using 1
  · funext w; ring
  · rfl

theorem anchoredVectorMoment_sub {d ℓ : ℕ} (u : Covariate d)
    (p g h : Covariate d → ℝ) (hpmeas : Measurable p) (b : ℝ)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (hh : ContinuousOn h (unitCube d)) :
    anchoredVectorMoment (ℓ := ℓ) u p (g - h) =
      anchoredVectorMoment u p g - anchoredVectorMoment u p h := by
  ext γ
  change (∫ w, p w * anchoredFeature u w γ * (g w - h w) ∂cubeVolume d) = _
  simp only [mul_sub]
  exact integral_sub (anchoredVectorMoment_integrable u p g hpmeas b hp hg γ)
    (anchoredVectorMoment_integrable u p h hpmeas b hp hh γ)

theorem anchoredPopulationFit_error_equation {d ℓ : ℕ} (u : Covariate d)
    (p g : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredDensityGram u p *ᵥ (anchoredPopulationFit u p g - c) =
      anchoredVectorMoment u p (g - anchoredFitPolynomial u c) := by
  rw [Matrix.mulVec_sub, anchoredPopulationFit_normal_equation u p g hpmeas a b ha hp,
    anchoredVectorMoment_sub u p g _ hpmeas b
      (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hg
      (anchoredFitPolynomial_continuous u c).continuousOn,
    anchoredVectorMoment_polynomial u p hpmeas b
      (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩))]

theorem anchoredDensityGram_solve_norm_bound {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b cB : ℝ)
    (ha : 0 < a) (hcB : 0 < cB)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hB : ∀ c : AnchoredCoefficientSpace d ℓ,
      cB * ‖c‖ ^ 2 ≤ anchoredQuadratic u c)
    (e r : AnchoredIndex d ℓ → ℝ) (her : anchoredDensityGram u p *ᵥ e = r) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm e‖ ≤
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm r‖ / (a * cB) := by
  let E := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm e
  let R := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm r
  have hq := (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha.le hp e).1
  have hb := hB E
  have hinner : e ⬝ᵥ r ≤ ‖E‖ * ‖R‖ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, E, R,
      EuclideanSpace.equiv]
      using real_inner_le_norm E R
  have hcoer : a * cB * ‖E‖ ^ 2 ≤ e ⬝ᵥ r := by
    calc
      a * cB * ‖E‖ ^ 2 = a * (cB * ‖E‖ ^ 2) := by ring
      _ ≤ a * anchoredQuadratic u E := mul_le_mul_of_nonneg_left hb ha.le
      _ ≤ e ⬝ᵥ r := by simpa [anchoredQuadratic, her, E, EuclideanSpace.equiv] using hq
  change ‖E‖ ≤ ‖R‖ / (a * cB)
  by_cases he : ‖E‖ = 0
  · rw [he]; positivity
  · have hpos : 0 < ‖E‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    apply (le_div_iff₀ (mul_pos ha hcB)).2
    nlinarith

/-- A uniform coefficient-error constant derived from density bounds and the
known Gram. The approximation premise is solely a genuine polynomial residual. -/
theorem anchoredPopulationFit_coefficient_error {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g : Covariate d → ℝ,
      Measurable p → (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c : AnchoredIndex d ℓ → ℝ,
      ∀ R : ℝ, 0 ≤ R → (∀ w ∈ unitCube d, |g w - anchoredFitPolynomial u c w| ≤ R) →
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredPopulationFit u p g - c)‖ ≤ D * R := by
  obtain ⟨cB, CB, hcB, hCB, hGram⟩ := anchoredGram_uniform_bounds (d := d) (ℓ := ℓ)
  let D := max 1 (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * b / (a * cB))
  refine ⟨D, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres
  have heq := anchoredPopulationFit_error_equation u p g hpmeas a b ha hp hg c
  have he := anchoredDensityGram_solve_norm_bound u p hpmeas a b cB ha hcB hp
    (fun v => (hGram u hu v).1) _ _ heq
  have hr := anchoredVectorMoment_norm_bound (ℓ := ℓ) u hu p (g - anchoredFitPolynomial u c)
    b R hb hR (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hres
  apply he.trans
  calc
    _ ≤ (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * R)) / (a * cB) :=
      div_le_div_of_nonneg_right hr (mul_pos ha hcB).le
    _ = (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * b / (a * cB)) * R := by ring
    _ ≤ D * R := mul_le_mul_of_nonneg_right (le_max_right _ _) hR

theorem anchoredFitPolynomial_abs_le_distance {d ℓ : ℕ} (u w : Covariate d)
    (hu : u ∈ unitCube d) (hw : w ∈ unitCube d) (c : AnchoredIndex d ℓ → ℝ) :
    |anchoredFitPolynomial u c w| ≤ (Fintype.card (AnchoredIndex d ℓ) : ℝ) *
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ * euclideanNorm (w - u) := by
  calc
    _ ≤ ∑ γ, |c γ * anchoredFeature u w γ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _γ : AnchoredIndex d ℓ,
        ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ * euclideanNorm (w - u) := by
      apply Finset.sum_le_sum
      intro γ _
      rw [abs_mul]
      apply mul_le_mul _ (anchoredFeature_abs_le_euclideanNorm u w hu hw γ)
        (abs_nonneg _) (norm_nonneg _)
      simpa [Real.norm_eq_abs, EuclideanSpace.equiv] using
        PiLp.norm_apply_le ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c) γ
    _ = _ := by simp; ring

theorem anchoredFitPolynomial_sub {d ℓ : ℕ} (u w : Covariate d)
    (c e : AnchoredIndex d ℓ → ℝ) :
    anchoredFitPolynomial u (c - e) w = anchoredFitPolynomial u c w - anchoredFitPolynomial u e w := by
  simp only [anchoredFitPolynomial, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The coefficient estimate yields the spatial Lipschitz-at-anchor error term
needed by the actual population fit, without an assumed fitted-coefficient bound. -/
theorem anchoredPopulationFit_pointwise_error {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g : Covariate d → ℝ,
      Measurable p → (∀ᵐ v ∂cubeVolume d, a ≤ p v ∧ p v ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c : AnchoredIndex d ℓ → ℝ,
      ∀ R : ℝ, 0 ≤ R → (∀ v ∈ unitCube d, |g v - anchoredFitPolynomial u c v| ≤ R) →
      ∀ w ∈ unitCube d,
      |g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w| ≤
        |g w - anchoredFitPolynomial u c w| + D * R * euclideanNorm (w - u) := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := ℓ) a b ha hb
  let E := max 1 ((Fintype.card (AnchoredIndex d ℓ) : ℝ) * D)
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres w hw
  have hcoeff := hfit u hu p g hpmeas hp hg c R hR hres
  have hpoly := anchoredFitPolynomial_abs_le_distance u w hu hw (anchoredPopulationFit u p g - c)
  have hnonneg : 0 ≤ euclideanNorm (w - u) := by unfold euclideanNorm; positivity
  have habs : |anchoredFitPolynomial u (anchoredPopulationFit u p g - c) w| ≤
      E * R * euclideanNorm (w - u) := by
    apply hpoly.trans
    calc
      _ ≤ (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (D * R) * euclideanNorm (w - u) := by
        gcongr
      _ = ((Fintype.card (AnchoredIndex d ℓ) : ℝ) * D) * R * euclideanNorm (w - u) := by ring
      _ ≤ E * R * euclideanNorm (w - u) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) hnonneg
  have heq : g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w =
      (g w - anchoredFitPolynomial u c w) -
        anchoredFitPolynomial u (anchoredPopulationFit u p g - c) w := by
    rw [anchoredFitPolynomial_sub]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add le_rfl habs)

end NearlyMinimax
