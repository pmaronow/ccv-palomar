module

public import NearlyMinimax.DyadicPilotLift


@[expose] public section

/-! Genuine clipped dyadic grid nesting, including the cube's right boundary. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax

theorem regular_grid_same_cell_congr {d k l : ℕ} (h : k = l) (hk : 0 < k) (hl : 0 < l)
    (x z : Covariate d) : (regularGridCell k hk z = regularGridCell k hk x) ↔
      (regularGridCell l hl z = regularGridCell l hl x) := by
  subst l
  rfl

theorem regular_grid_index_parent (k : ℕ) (hk : 0 < k) (x : ℝ) :
    (regularGridIndex (2 * k) (by omega) x).val / 2 = (regularGridIndex k hk x).val := by
  have hre : ((2 * k : ℕ) : ℝ) * x = ((k : ℝ) * x) * (2 : ℕ) := by push_cast; ring
  have hf : ⌊((2 * k : ℕ) : ℝ) * x⌋₊ / 2 = ⌊(k : ℝ) * x⌋₊ := by
    rw [hre, Nat.mul_cast_floor_div_cancel (by decide : (2 : ℕ) ≠ 0)]
  simp only [regularGridIndex, Fin.val_mk]
  omega

/-- A genuine fine-cell equality implies equality of the dyadic parent labels. -/
theorem regular_grid_cell_parent_eq {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x z : Covariate d)
    (h : regularGridCell (2 * k) (by omega) z = regularGridCell (2 * k) (by omega) x) :
    regularGridCell k hk z = regularGridCell k hk x := by
  funext i
  apply Fin.ext
  have hi := congrArg (fun c => (c i).val / 2) h
  change (regularGridIndex (2 * k) (by omega) (z i)).val / 2 =
    (regularGridIndex (2 * k) (by omega) (x i)).val / 2 at hi
  rw [regular_grid_index_parent k hk, regular_grid_index_parent k hk] at hi
  exact hi

theorem dyadicPilotCell_subset_parent {d : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicPilotCell j x ⊆ dyadicPilotCell (j - 1) x := by
  cases j with
  | zero => simp
  | succ j =>
    intro z hz
    apply regular_grid_cell_parent_eq ((2 : ℕ) ^ j) (by positivity) x z
    change regularGridCell ((2 : ℕ) ^ (j + 1)) (by positivity) z =
      regularGridCell ((2 : ℕ) ^ (j + 1)) (by positivity) x at hz
    have hsize : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
    exact (regular_grid_same_cell_congr hsize (by positivity) (by positivity) x z).mp hz

end NearlyMinimax
