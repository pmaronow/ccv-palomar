module

public import NearlyMinimax.DyadicPilotPointwise
public import NearlyMinimax.PairDesignMarginal


@[expose] public section

/-! Actual pre-centering parent-cell support and original weighted-pair
design localization. These are the geometric inputs of U7. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem preconditionedPilotFeature_zero_off_cell {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) (hz : z.1 ∉ dyadicPilotCell j x) :
    preconditionedPilotFeature j x a z = 0 := by
  simp [preconditionedPilotFeature, dyadicPilotFeature, hz]

theorem dyadicIncrementRawVector_zero_off_parent {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (z : Observation d) (hz : z.1 ∉ dyadicPilotCell (j - 1) x) :
    dyadicIncrementRawVector (ℓ := ℓ) j x z = 0 := by
  have hj : j ≠ 0 := by
    intro h
    subst j
    apply hz
    change regularGridCell 1 (by positivity) z.1 = regularGridCell 1 (by positivity) x
    exact Subsingleton.elim _ _
  have hcur : z.1 ∉ dyadicPilotCell j x := fun h => hz (dyadicPilotCell_subset_parent j x h)
  funext a
  change dyadicIncrementFeature j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) z = 0
  generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a = v
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      exact preconditionedPilotFeature_zero_off_cell j x _ z hcur
    | inr v =>
      simpa only [dyadicIncrementFeature, if_neg hj] using
        preconditionedPilotFeature_zero_off_cell (j - 1) x
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z hz
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent <;> cases response
    all_goals first
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell j x (Sum.inr (Sum.inl (anchoredFinIndex i))) z hcur
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell j x (Sum.inr (Sum.inr (anchoredFinIndex i))) z hcur
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell (j - 1) x (Sum.inr (Sum.inl (anchoredFinIndex i))) z hz
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell (j - 1) x (Sum.inr (Sum.inr (anchoredFinIndex i))) z hz

theorem dyadic_increment_raw_kernel_zero_off_parent {d ℓ k : ℕ} (j : ℕ) (x : Covariate d)
    (H : ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) ℝ)
    (z : Fin k → Observation d) (i : Fin k) (hz : (z i).1 ∉ dyadicPilotCell (j - 1) x) :
    H (fun t => dyadicIncrementRawVector j x (z t)) = 0 :=
  H.map_coord_zero i (dyadicIncrementRawVector_zero_off_parent j x (z i) hz)

/-- Raw derivative kernels on different actual parent cells are orthogonal
before any centering. No covariance orthogonality is postulated. -/
theorem dyadic_increment_raw_kernels_disjoint {d ℓ k : ℕ} (hk : 0 < k)
    (j : ℕ) (x y : Covariate d)
    (hcell : dyadicPilotLabel (j - 1) x ≠ dyadicPilotLabel (j - 1) y)
    (H G : ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) ℝ)
    (z : Fin k → Observation d) :
    H (fun t => dyadicIncrementRawVector j x (z t)) *
      G (fun t => dyadicIncrementRawVector j y (z t)) = 0 := by
  let i : Fin k := ⟨0, hk⟩
  by_cases hz : (z i).1 ∈ dyadicPilotCell (j - 1) x
  · have hzy : (z i).1 ∉ dyadicPilotCell (j - 1) y := by
      intro h
      apply hcell
      exact ((dyadicPilotLabel_eq_iff (j - 1) x (z i).1).mpr hz).symm.trans
        ((dyadicPilotLabel_eq_iff (j - 1) y (z i).1).mpr h)
    rw [dyadic_increment_raw_kernel_zero_off_parent j y G z i hzy, mul_zero]
  · rw [dyadic_increment_raw_kernel_zero_off_parent j x H z i hz, zero_mul]

/-- Each actual parent-anchor block has weighted-pair mass at most
`p₊² / K_parent`, the localization gain required by U7. -/
theorem regularPairDesignMeasure_parent_block_mass {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) (j : ℕ)
    (c : Fin d → Fin ((2 : ℕ) ^ (j - 1))) :
    (regularPairDesignMeasure θ k hk).real
      {w : Covariate d × Covariate d | regularGridCell ((2 : ℕ) ^ (j - 1)) (by positivity) w.1 = c} ≤
        C.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
  let := cubeVolume_isProbability d
  let A : Set (Covariate d) := (regularGridCell ((2 : ℕ) ^ (j - 1)) (by positivity)) ⁻¹' {c}
  have hA : MeasurableSet A := measurableSet_singleton c |>.preimage (regular_grid_cell_measurable _ _)
  have hmap := regularPairDesignMeasure_fst_cube_le C θ hθ k hk
  have hfirst : (regularPairDesignMeasure θ k hk).real (Prod.fst ⁻¹' A) ≤
      C.densityUpper ^ 2 * (cubeVolume d).real A := by
    rw [← map_measureReal_apply measurable_fst hA]
    have ht := ENNReal.toReal_mono
      (show (ENNReal.ofReal (C.densityUpper ^ 2) • cubeVolume d) A ≠ ⊤ by
        simp only [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (cubeVolume d) A))
      (hmap A)
    simpa only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)] using ht
  have hvol : (cubeVolume d).real A ≤ (1 / ((2 : ℝ) ^ (j - 1))) ^ d := by
    have hv := regular_grid_fiber_volume_le ((2 : ℕ) ^ (j - 1)) (by positivity) c
    have ht := ENNReal.toReal_mono (by finiteness :
      ENNReal.ofReal (1 / (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ)) ^ d ≠ ⊤) hv
    simpa [measureReal_def, A, ENNReal.toReal_pow, Nat.cast_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ))] using ht
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_left hvol (sq_nonneg _)).trans_eq
  simp only [dyadicPilotScale, div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow]

end NearlyMinimax
