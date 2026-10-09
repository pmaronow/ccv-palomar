module

public import NearlyMinimax.IncrementPilotKernels
public import NearlyMinimax.DyadicTaylor


@[expose] public section

/-! Genuine physical feature-row factors for the sharp pair pilot. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem dyadicPilotCell_subset_coarser {d : ℕ} (j J : ℕ) (hj : j ≤ J) (x : Covariate d) :
    dyadicPilotCell J x ⊆ dyadicPilotCell j x := by
  induction J with
  | zero =>
    have he : j = 0 := by omega
    subst j
    exact subset_rfl
  | succ J ih =>
    by_cases he : j = J + 1
    · subst j
      exact subset_rfl
    · intro z hz
      apply ih (by omega)
      simpa using dyadicPilotCell_subset_parent (J + 1) x hz

theorem dyadicAnchoredFeature_abs_le_distance {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell j x)
    (γ : AnchoredIndex d ℓ) :
    |dyadicAnchoredFeature j x z γ| ≤ (2 : ℝ) ^ j * euclideanNorm (z - x) := by
  have hv (i : Fin d) : |((2 : ℝ) ^ j • (z - x)) i| ≤ 1 := by
    have hr := regular_grid_same_cell_radius ((2 : ℕ) ^ j) (by positivity) z x hz hx hc i
    have he : (((2 : ℕ) ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by simp
    rw [he] at hr
    change |(2 : ℝ) ^ j * (z i - x i)| ≤ 1
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq (by field_simp)
  have h := anchoredMonomial_abs_le_euclideanNorm γ ((2 : ℝ) ^ j • (z - x)) hv
  rw [euclideanNorm_smul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j)] at h
  exact h

def dyadicPilotRow {d ℓ : ℕ} (j : ℕ) (x z : Covariate d) : Fin (anchoredDimension d ℓ) → ℝ :=
  fun i => dyadicAnchoredFeature j x z (anchoredFinIndex i)

theorem dyadicPilotRow_sum_abs_le_distance {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell j x) :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * euclideanNorm (z - x) := by
  apply (Finset.sum_le_sum (fun i _ => dyadicAnchoredFeature_abs_le_distance j x z hx hz hc _)).trans_eq
  simp [mul_assoc]

/-- Every feature row for a coarser pilot satisfies its genuine `h 2^j`
factor on the actual finest dyadic same-cell pair support. -/
theorem dyadicPilotRow_sum_abs_le_fine_cell {d ℓ : ℕ} (j J : ℕ) (hj : j ≤ J)
    (x z : Covariate d) (hx : x ∈ unitCube d) (hz : z ∈ unitCube d)
    (hc : z ∈ dyadicPilotCell J x) :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ := by
  apply (dyadicPilotRow_sum_abs_le_distance j x z hx hz
    (dyadicPilotCell_subset_coarser j J hj x hc)).trans
  have hr := euclideanNorm_le_coordinate_radius (z - x) (1 / (((2 : ℕ) ^ J : ℕ) : ℝ))
    (by positivity) (regular_grid_same_cell_radius ((2 : ℕ) ^ J) (by positivity) z x hz hx hc)
  apply (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq
  simp [mul_assoc]

end NearlyMinimax
