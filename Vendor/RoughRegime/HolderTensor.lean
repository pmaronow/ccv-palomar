module

public import RoughRegime.HolderModulus


@[expose] public section

/-! Ordered coordinate derivatives control genuine multilinear operator norms. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.Model

lemma euclidean_coordinate_decomposition {d : ℕ} (x : Covariate d) :
    x = ∑ i : Fin d, x i • EuclideanSpace.single i (1 : ℝ) := by
  classical
  ext j
  simp [Pi.single_apply]

theorem multilinear_coordinate_expansion {d q : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (v : Fin q → Covariate d) :
    L v = ∑ σ : Fin q → Fin d, (∏ i, v i (σ i)) *
      L (fun i => EuclideanSpace.single (σ i) (1 : ℝ)) := by
  classical
  have hv : v = fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j (1 : ℝ) := by
    funext i
    exact euclidean_coordinate_decomposition (v i)
  conv_lhs => rw [hv]
  change L.toMultilinearMap (fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j (1 : ℝ)) = _
  rw [L.toMultilinearMap.map_sum]
  simp only [L.toMultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem multilinear_norm_le_coordinate_bound {d q : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (H : ℝ) (hH : 0 ≤ H)
    (hb : ∀ σ : Fin q → Fin d, |L (fun i => EuclideanSpace.single (σ i) 1)| ≤ H) :
    ‖L‖ ≤ (d : ℝ) ^ q * H := by
  classical
  apply L.opNorm_le_bound (by positivity)
  intro v
  rw [multilinear_coordinate_expansion]
  calc
    _ ≤ ∑ σ : Fin q → Fin d,
        ‖(∏ i, v i (σ i)) * L (fun i => EuclideanSpace.single (σ i) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Fin q → Fin d, (∏ i, ‖v i‖) * H := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, Real.norm_eq_abs, Finset.abs_prod]
      apply mul_le_mul _ (hb σ) (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i) (σ i))
    _ = ((d : ℝ) ^ q * H) * ∏ i, ‖v i‖ := by simp; ring

theorem holderBall_iteratedFDerivWithin_bound {d : ℕ} (f : Covariate d → ℝ)
    (t H : ℝ) (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
    (q : ℕ) (hq : q ≤ holderOrder t) (x : Covariate d) (hx : x ∈ cube d) :
    ‖iteratedFDerivWithin ℝ q f (cube d) x‖ ≤ (d : ℝ) ^ q * H := by
  apply multilinear_norm_le_coordinate_bound _ H hH
  intro σ
  exact holderBall_coordinate_bound f t H hH hf q hq σ x hx

theorem holderBall_iteratedFDerivWithin_modulus {d : ℕ} (f : Covariate d → ℝ)
    (t H : ℝ) (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    ‖iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x -
      iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y‖ ≤
      (d : ℝ) ^ holderOrder t * H * ‖x - y‖ ^ holderExponent t := by
  have hbound := multilinear_norm_le_coordinate_bound
    (iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x -
      iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y)
    (H * ‖x - y‖ ^ holderExponent t) (by positivity) (fun σ => by
      simpa only [sub_apply, coordinateDerivative] using
        holderBall_coordinate_modulus f t H hH hf σ x y hx hy)
  simpa only [mul_assoc] using hbound

end RoughRegime.Model
