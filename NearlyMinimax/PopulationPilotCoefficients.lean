module

public import NearlyMinimax.PopulationPilotMeans


@[expose] public section

/-! Original multiscale mean coefficient vector, its uniform cap, Borel
measurability, and exact residual identity. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped RealInnerProductSpace BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def dyadicPopulationPilotSum {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (t : Bool) (w : Covariate d × Covariate d) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j w.1 w.2 ⬝ᵥ dyadicPopulationRawPolynomial C θ j w.1 t (m j)

def dyadicPopulationCoefficients {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (w : Covariate d × Covariate d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + dyadicPopulationPilotSum C θ J m true w,
    -dyadicPopulationPilotSum C θ J m false w]

theorem finite_row_abs_dot_le_pi_norm {ι : Type*} [Fintype ι] (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖v‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i, |row i * v i|) ≤ ∑ i, |row i| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem dyadic_geometric_sum_le (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ (J + 1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ _ (J + 1)]
    linarith

theorem dyadicPilotRow_total_abs_le {d ℓ : ℕ} (J : ℕ) (x y : Covariate d)
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) (hc : y ∈ dyadicPilotCell J x) :
    (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := ℓ) j x y i|) ≤
      2 * (anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1),
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      exact dyadicPilotRow_sum_abs_le_fine_cell j J (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x y hx hy hc
    _ = ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) *
      ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) * (2 : ℝ) ^ (J + 1) :=
      mul_le_mul_of_nonneg_left (dyadic_geometric_sum_le J) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

theorem admissible_dyadicPopulationPilotSum_uniform_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ∀ t : Bool, |dyadicPopulationPilotSum C θ J m t (x, y)| ≤ R := by
  obtain ⟨B, hB, hb⟩ := admissible_dyadicPopulationRawPolynomial_uniform_bound C hs
  let R := (2 * (anchoredDimension d C.order : ℝ) * Real.sqrt (d : ℝ)) * B
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  intro θ hθ J m x hx y hy hcell t
  unfold dyadicPopulationPilotSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), (∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
      apply Finset.sum_le_sum
      intro j hj
      exact (finite_row_abs_dot_le_pi_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hb θ hθ j x hx t (m j)) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    _ = (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
      rw [Finset.sum_mul]
    _ ≤ R := mul_le_mul_of_nonneg_right (dyadicPilotRow_total_abs_le J x y hx hy hcell) hB.le

theorem admissible_dyadicPopulationCoefficients_uniform_bound {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ‖dyadicPopulationCoefficients C θ J m (x, y)‖ ≤ Cp := by
  obtain ⟨R, hR, hb⟩ := admissible_dyadicPopulationPilotSum_uniform_bound C hs
  refine ⟨Real.sqrt 3 * (1 + R), mul_pos (by positivity) (by positivity), ?_⟩
  intro θ hθ J m x hx y hy hc
  have ht := hb θ hθ J m x hx y hy hc true
  have hf := hb θ hθ J m x hx y hy hc false
  have hcoord (i : Fin 3) : |dyadicPopulationCoefficients C θ J m (x, y) i| ≤ 1 + R := by
    fin_cases i
    · simpa [dyadicPopulationCoefficients] using hR
    · change |-1 + dyadicPopulationPilotSum C θ J m true (x, y)| ≤ 1 + R
      exact (abs_add_le _ _).trans (by simpa using add_le_add_left ht 1)
    · change |-dyadicPopulationPilotSum C θ J m false (x, y)| ≤ 1 + R
      rw [abs_neg]
      exact hf.trans (by linarith)
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc
    (∑ i : Fin 3, ‖dyadicPopulationCoefficients C θ J m (x, y) i‖ ^ 2) ≤ ∑ _i : Fin 3, (1 + R) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hcoord i) 2
    _ = 3 * (1 + R) ^ 2 := by simp
    _ = (Real.sqrt 3 * (1 + R)) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]

theorem dyadicPopulationCoefficients_residual {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (J : ℕ) (m : ℕ → ℕ) (x y : Covariate d) :
    ⟪dyadicPopulationCoefficients C θ J m (x, y), pairResponseVector (θ.regression x) (θ.regression y)⟫ =
      dyadicPopulationResidual C θ J m x y := by
  have hsum : (∑ j ∈ Finset.range (J + 1),
      dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) =
      dyadicPopulationPilotSum C θ J m false (x, y) -
        θ.regression x * dyadicPopulationPilotSum C θ J m true (x, y) := by
    simp only [dyadicPopulationPolynomial_affine, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Finset.sum_sub_distrib, dyadicPopulationPilotSum]
    rw [Finset.mul_sum]
  rw [pairResponseVector_inner]
  change 1 * θ.regression y + (-1 + dyadicPopulationPilotSum C θ J m true (x, y)) * θ.regression x +
    (-dyadicPopulationPilotSum C θ J m false (x, y)) = dyadicPopulationResidual C θ J m x y
  unfold dyadicPopulationResidual
  rw [hsum]
  ring

theorem dyadicPopulationRawPolynomial_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (t : Bool) (m : ℕ) :
    Measurable (fun x => dyadicPopulationRawPolynomial C θ j x t m) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (MvPolynomial.continuous_eval (MvPolynomial.rename
    (Fintype.equivFin (incrementVariables (anchoredDimension d C.order)))
      (rawIncrementEntryPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) t m i))).measurable.comp
      (dyadicIncrementRawMean_measurable C θ hθ j)

theorem dyadicPopulationPilotSum_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (J : ℕ) (m : ℕ → ℕ) (t : Bool) :
    Measurable (dyadicPopulationPilotSum C θ J m t) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro i _
  exact (dyadicAnchoredFeature_joint_measurable j (anchoredFinIndex i)).mul
    (((dyadicPopulationRawPolynomial_measurable C θ hθ j t (m j)).eval (a := i)).comp measurable_fst)

theorem dyadicPopulationCoefficients_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (J : ℕ) (m : ℕ → ℕ) :
    Measurable (dyadicPopulationCoefficients C θ J m) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add (dyadicPopulationPilotSum_measurable C θ hθ J m true)
  · exact (dyadicPopulationPilotSum_measurable C θ hθ J m false).neg

end NearlyMinimax
