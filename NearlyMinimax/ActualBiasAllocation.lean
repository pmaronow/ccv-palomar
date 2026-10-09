module

public import NearlyMinimax.PolynomialGaussian
public import NearlyMinimax.DegreeBounds


@[expose] public section

/-!
# The finite scalar bias bound for the actual upper allocation

This module composes the explicit candidate width, terminal dyadic flooring,
coordinate-degree subtraction, Gaussian absorption and uniform lattice sum.
Unlike the abstract allocation lemma, the final theorem has no level-range,
degree, summand, or bias-sum hypotheses. Its hypotheses concern only the fixed
positive allocation constants and the two scalar coefficient identities.
This is a scalar allocation theorem, not a statistical risk theorem.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace NearlyMinimax

/-- The exact degree `m_j=floor(beta Q_S(z_j))-q` at the explicit level position. -/
def actualApproximationDegree (δ a C H β x : ℝ) (j q : ℕ) : ℕ :=
  allocatedApproximationDegree β (allocationWidth a C x) (allocationLevelPosition δ a C H x j) q

/-- `eq:U12-sum` for the actual floored scalar allocation, for all sufficiently large sample sizes. -/
theorem eventually_actual_allocation_bias_sum (r q : ℕ) (δ a C H γ β θ τ : ℝ)
    (hδ : 0 < δ) (ha : 0 < a) (hH : 0 < H) (hβ : 0 < β) (hθ : 0 < θ) (hτ : 0 < τ)
    (hθβ : τ * β = θ) (hθγ : θ * γ = (r : ℝ) + 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℝ in atTop,
      (∑ j ∈ Finset.range (terminalAllocationLevel δ a C H γ x + 1),
        (Real.exp (δ * (j : ℝ))) ^ (-θ) * ((actualApproximationDegree δ a C H β x j q : ℝ) + 1) ^ r *
          (Real.exp (-τ)) ^ (actualApproximationDegree δ a C H β x j q)) ≤
        B * (Real.exp (δ * (terminalAllocationLevel δ a C H γ x : ℝ))) ^ (-θ) := by
  refine ⟨allocationBiasSumConstant r q β θ τ δ,
    allocationBiasSumConstant_pos r q hβ.le hθ hδ, ?_⟩
  filter_upwards [(allocationWidth_tendsto_atTop ha C).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_terminal_cell_log_nonneg ha hH C γ,
    eventually_width_degree_threshold ha hβ C q] with x hS hLT hdegree
  let J := terminalAllocationLevel δ a C H γ x
  let S := allocationWidth a C x
  let ell := Real.log (H * S)
  let T := δ * (J : ℝ) - Real.log x
  let u₀ := -Real.log x + ell - S / 2
  let Kstar := Real.exp (δ * (J : ℝ))
  have hu := (roundedTerminalDepth_bounds hδ hLT).2
  change T ≤ S - ell - γ * Real.log S at hu
  have hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T) := by
    have hm := mul_le_mul_of_nonneg_left hu hθ.le
    have he : θ * γ * Real.log S = ((r : ℝ) + 1 / 2) * Real.log S := by rw [hθγ]
    nlinarith
  have hqS : (q : ℝ) ≤ β * S / 4 := by
    change (q : ℝ) + 2 ≤ β * S / 4 at hdegree
    linarith
  have hz (j : ℕ) : u₀ + (j : ℝ) * δ + S / 2 = allocationLevelPosition δ a C H x j := by
    unfold allocationLevelPosition
    dsimp [u₀, ell, S]
    ring
  have hbound := floored_raw_allocation_bias_sum_bound (Finset.range (J + 1)) r q
    u₀ δ β θ τ S ell T Kstar (fun j : ℕ => Real.exp (δ * (j : ℝ)))
    hδ hβ.le hθ hτ hS hθβ (Real.exp_pos _) (fun j hj => Real.exp_pos _) (by
      intro j hj
      dsimp [Kstar]
      rw [Real.log_exp, Real.log_exp]
      dsimp [u₀, T]
      ring) hreserve (by
      intro j hj
      exact profile_coordinate_order_admissible q hβ.le (by linarith : 0 < S) hqS)
  simp_rw [hz] at hbound
  simpa [actualApproximationDegree, J, Kstar] using hbound

end NearlyMinimax
