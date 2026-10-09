module

public import NearlyMinimax.Model
public import NearlyMinimax.Projection


@[expose] public section

open Set Matrix
open scoped BigOperators ENNReal

namespace NearlyMinimax

theorem multiPartial_zero_index {d : ℕ} (F : Covariate d → ℝ) :
    multiPartial F (fun _ => 0) = F := by
  have hflat : (List.finRange d).flatMap (fun _ => ([] : List (Fin d))) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  simp [multiPartial, hflat]

theorem euclideanNorm_eq_sqrt_energy {d : ℕ} (x : Covariate d) :
    euclideanNorm x = Real.sqrt (projectionEnergy x) := by
  simp only [euclideanNorm, projectionEnergy, dotProduct, pow_two]

theorem euclideanNorm_eq_zero_iff {d : ℕ} (x : Covariate d) :
    euclideanNorm x = 0 ↔ x = 0 := by
  rw [euclideanNorm_eq_sqrt_energy, Real.sqrt_eq_zero (projectionEnergy_nonneg x)]
  exact dotProduct_self_eq_zero

theorem euclideanNorm_pos_of_ne_zero {d : ℕ} (x : Covariate d) (hx : x ≠ 0) :
    0 < euclideanNorm x := by
  have hnonneg : 0 ≤ euclideanNorm x := by unfold euclideanNorm; positivity
  have hne : euclideanNorm x ≠ 0 := by
    intro hz
    exact hx ((euclideanNorm_eq_zero_iff x).mp hz)
  exact lt_of_le_of_ne hnonneg hne.symm

/-- The model's actual Hölder seminorm gives its pointwise modulus,
using precisely the Euclidean distance in the manuscript. -/
theorem holderSeminorm_pointwise_bound {d : ℕ} (U : Set (Covariate d))
    (G : Covariate d → ℝ) (α H : ℝ) (hH : 0 ≤ H)
    (hseminorm : holderSeminorm U G α ≤ ENNReal.ofReal H)
    (x y : Covariate d) (hx : x ∈ U) (hy : y ∈ U) :
    |G x - G y| ≤ H * euclideanNorm (x - y) ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, abs_zero]
    exact mul_nonneg hH (Real.rpow_nonneg (Real.sqrt_nonneg _) α)
  · have hraw : ENNReal.ofReal
        (|G x - G y| / euclideanNorm (x - y) ^ α) ≤ holderSeminorm U G α := by
      unfold holderSeminorm
      apply le_iSup_of_le (⟨x, hx⟩ : U)
      apply le_iSup_of_le (⟨y, hy⟩ : U)
      simp only [hxy, if_false]
      rfl
    have hquot := (ENNReal.ofReal_le_ofReal_iff hH).mp (hraw.trans hseminorm)
    have hdist : 0 < euclideanNorm (x - y) :=
      euclideanNorm_pos_of_ne_zero (x - y) (sub_ne_zero.mpr hxy)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hdist α)).mp hquot

/-- Every mixed partial counted in the model norm has the stated
uniform pointwise bound on the extension domain. -/
theorem holderNorm_derivative_bound {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (ℓ : ℕ) (α H : ℝ) (hH : 0 ≤ H)
    (hNorm : holderNorm U F ℓ α ≤ ENNReal.ofReal H)
    (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) ≤ ℓ)
    (x : Covariate d) (hx : x ∈ U) :
    |multiPartial F (fun i => (γ i).val) x| ≤ H := by
  have hpoint : ENNReal.ofReal |multiPartial F (fun i => (γ i).val) x| ≤
      derivativeSup U (multiPartial F (fun i => (γ i).val)) := by
    unfold derivativeSup
    exact le_iSup (fun z : U => ENNReal.ofReal |multiPartial F (fun i => (γ i).val) z|) ⟨x, hx⟩
  have hterm : derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤
      holderNorm U F ℓ α := by
    unfold holderNorm
    apply le_trans _ (le_add_right le_rfl)
    have ht := Finset.single_le_sum
      (fun δ (_ : δ ∈ Finset.univ) => (bot_le : (0 : ENNReal) ≤
        if (∑ i, (δ i).val) ≤ ℓ then derivativeSup U (multiPartial F (fun i => (δ i).val)) else 0))
      (Finset.mem_univ γ)
    simpa only [if_pos hγ] using ht
  exact (ENNReal.ofReal_le_ofReal_iff hH).mp ((hpoint.trans hterm).trans hNorm)

/-- The highest-order mixed partials counted by the model norm inherit
the actual Hölder modulus, without replacing the paper's norm. -/
theorem holderNorm_top_derivative_modulus {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (ℓ : ℕ) (α H : ℝ) (hH : 0 ≤ H)
    (hNorm : holderNorm U F ℓ α ≤ ENNReal.ofReal H)
    (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) = ℓ)
    (x y : Covariate d) (hx : x ∈ U) (hy : y ∈ U) :
    |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
      H * euclideanNorm (x - y) ^ α := by
  apply holderSeminorm_pointwise_bound U _ α H hH _ x y hx hy
  apply le_trans _ hNorm
  unfold holderNorm
  apply le_trans _ (le_add_left le_rfl)
  apply le_iSup_of_le γ
  simp only [if_pos hγ]
  exact le_rfl

/-- At order zero, the model norm is precisely the function supremum
and its Hölder seminorm. -/
theorem holderNorm_order_zero {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (α : ℝ) :
    holderNorm U F 0 α = derivativeSup U F + holderSeminorm U F α := by
  have hflat : (List.finRange d).flatMap (fun _ => ([] : List (Fin d))) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  simp [holderNorm, multiPartial, hflat]

/-- The paper's actual admissibility norm bounds the regression values
uniformly on the design cube for every smoothness order. -/
theorem admissible_regression_value_bound {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (x : Covariate d) (hx : x ∈ unitCube d) : |θ.regression x| ≤ C.holderBound := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, _, hNorm⟩, _, _, _⟩
  have hb := holderNorm_derivative_bound C.domain F C.order C.alpha C.holderBound
    C.holderBound_pos.le hNorm (fun _ => 0) (by simp) x (C.cube_subset hx)
  simpa only [Fin.val_zero, multiPartial_zero_index, hcube x hx] using hb

/-- At smoothness order zero the actual admissible regression has the
pointwise Hölder modulus needed for cellwise constant approximation. -/
theorem admissible_regression_order_zero_modulus {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (horder : C.order = 0)
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) :
    |θ.regression x - θ.regression y| ≤
      C.holderBound * euclideanNorm (x - y) ^ C.smoothness := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, _, hNorm⟩, _, _, _⟩
  rw [horder, holderNorm_order_zero] at hNorm
  have hseminorm : holderSeminorm C.domain F C.alpha ≤ ENNReal.ofReal C.holderBound :=
    (le_add_left le_rfl).trans hNorm
  have hm := holderSeminorm_pointwise_bound C.domain F C.alpha C.holderBound
    C.holderBound_pos.le hseminorm x y (C.cube_subset hx) (C.cube_subset hy)
  have hα : C.alpha = C.smoothness := by simp [ModelConstants.alpha, horder]
  simpa only [hα, hcube x hx, hcube y hy] using hm

/-- A cube of side length `h` has Euclidean diameter at most `sqrt(d) h`. -/
theorem euclideanNorm_le_coordinate_radius {d : ℕ} (x : Covariate d)
    (h : ℝ) (hh : 0 ≤ h) (hx : ∀ i, |x i| ≤ h) :
    euclideanNorm x ≤ Real.sqrt (d : ℝ) * h := by
  rw [euclideanNorm, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hh, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  calc
    (∑ i, x i ^ 2) ≤ ∑ _i : Fin d, h ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hh).mpr (hx i)
    _ = _ := by simp

end NearlyMinimax
