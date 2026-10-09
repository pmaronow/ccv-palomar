module

public import NearlyMinimax.HighDesignScoreTransfer
public import NearlyMinimax.HighNormalizedCounts


@[expose] public section

/-! The actual iid membership partition gives the finite factorial
score-energy series. The selected-observation spatial integrals remain
explicit, so this bridge does not assume a global score budget. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

theorem finset_sum_cardinality {n : ℕ} (F : ℕ → ℝ) :
    (∑ S : Finset (Fin n), F S.card) =
      ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * F r := by
  have h := Finset.sum_powerset (Finset.univ : Finset (Fin n)) (fun S => F S.card)
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r hr
  simpa only [Finset.sum_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] using
      (Finset.sum_powersetCard r (Finset.univ : Finset (Fin n)) F)

theorem iid_local_energy_le_binomial_spatial_series {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (E : (Fin n → α) → ℝ) (hE : Integrable E (Measure.pi (fun _ : Fin n => μ)))
    (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S (fun i : S => x i.val))
    (ψ : ℝ) (J : ℕ → ℝ)
    (hspatial : ∀ S : Finset (Fin n), (∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A)) ≤ ψ ^ S.card * J S.card) :
    (∫ x, E x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * ψ ^ r * J r := by
  calc
    _ ≤ ∑ S : Finset (Fin n), ∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A) :=
      iid_local_energy_le_selected_sum μ n A hA E hE H hH hHn hdom
    _ ≤ ∑ S : Finset (Fin n), ψ ^ S.card * J S.card :=
      Finset.sum_le_sum (fun S _ => hspatial S)
    _ = _ := by
      rw [finset_sum_cardinality (fun r => ψ ^ r * J r)]
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem iid_local_energy_le_factorial_spatial_series {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (E : (Fin n → α) → ℝ) (hE : Integrable E (Measure.pi (fun _ : Fin n => μ)))
    (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S (fun i : S => x i.val))
    (ψ : ℝ) (hψ : 0 ≤ ψ) (J : ℕ → ℝ) (hJ : ∀ r, 0 ≤ J r)
    (hspatial : ∀ S : Finset (Fin n), (∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A)) ≤ ψ ^ S.card * J S.card) :
    (∫ x, E x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ r ∈ Finset.range (n + 1), ((n : ℝ) * ψ) ^ r / (r.factorial : ℝ) * J r := by
  refine (iid_local_energy_le_binomial_spatial_series μ n A hA E hE H hH hHn hdom ψ J hspatial).trans ?_
  apply Finset.sum_le_sum
  intro r hr
  calc
    _ ≤ ((n : ℝ) ^ r / (r.factorial : ℝ)) * ψ ^ r * J r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div r n) (pow_nonneg hψ r)) (hJ r)
    _ = _ := by rw [mul_pow]; ring

end NearlyMinimax
