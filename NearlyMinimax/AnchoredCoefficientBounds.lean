module

public import NearlyMinimax.PilotCoordinateExpansion
public import NearlyMinimax.AnchoredGramBounds


@[expose] public section

/-! Fixed-level uniform coefficient bounds used only for spatial integrability.
The sharp moment budget is supplied separately by the actual pilot moments. -/

noncomputable section
open Set MvPolynomial
namespace NearlyMinimax

/-- A finite continuous scalar family has one positive bound on the cube. -/
theorem finiteContinuousFamily_uniform_cube_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Covariate d → ι → ℝ) (hf : ∀ i, Continuous (fun x => f x i)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ i, |f x i| ≤ M := by
  have hc : Continuous f := continuous_pi hf
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.norm.continuousOn
  refine ⟨max 1 M, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx i
  have hi : |f x i| ≤ ‖f x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f x) i
  exact hi.trans ((hM (mem_image_of_mem _ hx)).trans (le_max_right _ _))

theorem dyadicFeaturePolynomial_coeff_uniform_bound {d ℓ : ℕ} (j r : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ γ : AnchoredIndex d ℓ,
      ∀ β : PolynomialBox d r,
        |(dyadicFeaturePolynomial j x γ).coeff (polynomialBoxExponent β)| ≤ M := by
  obtain ⟨M, hM, hb⟩ := finiteContinuousFamily_uniform_cube_bound
    (fun x (i : AnchoredIndex d ℓ × PolynomialBox d r) =>
      (dyadicFeaturePolynomial j x i.1).coeff (polynomialBoxExponent i.2))
    (fun i => dyadicFeaturePolynomial_coeff_continuous j i.1 _)
  exact ⟨M, hM, fun x hx γ β => hb x hx (γ, β)⟩

theorem dyadicFeatureProduct_coeff_uniform_bound {d ℓ : ℕ} (j r : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ γ δ : AnchoredIndex d ℓ,
      ∀ β : PolynomialBox d r,
        |(dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ).coeff
          (polynomialBoxExponent β)| ≤ M := by
  obtain ⟨M, hM, hb⟩ := finiteContinuousFamily_uniform_cube_bound
    (fun x (i : AnchoredIndex d ℓ × AnchoredIndex d ℓ × PolynomialBox d r) =>
      (dyadicFeaturePolynomial j x i.1 * dyadicFeaturePolynomial j x i.2.1).coeff
        (polynomialBoxExponent i.2.2))
    (fun i => dyadicFeatureProduct_coeff_continuous j i.1 i.2.1 _)
  exact ⟨M, hM, fun x hx γ δ β => hb x hx (γ, δ, β)⟩

theorem dyadicPilotPolynomial_coeff_continuous {d ℓ : ℕ} (j : ℕ)
    (a : LocalPilotIndex d ℓ) (e : Fin d →₀ ℕ) :
    Continuous (fun x : Covariate d => (dyadicPilotPolynomial j x a).coeff e) := by
  cases a with
  | inl a => exact dyadicFeatureProduct_coeff_continuous j a.1 a.2 e
  | inr a => cases a <;> exact dyadicFeaturePolynomial_coeff_continuous j _ e

/-- The entire finite raw pilot polynomial family is uniformly bounded at a
fixed level. This bound has no claimed uniformity in the level. -/
theorem dyadicPilotPolynomial_coeff_uniform_bound {d ℓ : ℕ} (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ∀ β : PolynomialBox d (2 * ℓ),
        |(dyadicPilotPolynomial j x a).coeff (polynomialBoxExponent β)| ≤ M := by
  obtain ⟨M, hM, hb⟩ := finiteContinuousFamily_uniform_cube_bound
    (fun x (i : LocalPilotIndex d ℓ × PolynomialBox d (2 * ℓ)) =>
      (dyadicPilotPolynomial j x i.1).coeff (polynomialBoxExponent i.2))
    (fun i => dyadicPilotPolynomial_coeff_continuous j i.1 _)
  exact ⟨M, hM, fun x hx a β => hb x hx (a, β)⟩

end NearlyMinimax
