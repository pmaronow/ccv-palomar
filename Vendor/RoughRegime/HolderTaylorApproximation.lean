module

public import RoughRegime.HolderTaylorLine


@[expose] public section

/-! The source Hölder hypothesis gives a genuine Taylor approximation error. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

lemma linePath_sub_base_norm_le {d : ℕ} (x y : Covariate d)
    (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : ‖linePath x y z - x‖ ≤ ‖y - x‖ := by
  simp only [linePath, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module',
    add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hz.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hz.2

@[simp] lemma holderTaylorPolynomial_zero_eval {d : ℕ} (f : Covariate d → ℝ)
    (x y : Covariate d) : MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f 0 x) = f x := by
  simp [holderTaylorPolynomial, multilinearPolynomial_eval, iteratedFDerivWithin_zero_apply]

theorem holderTaylorPolynomial_error {d : ℕ} (f : Covariate d → ℝ)
    (t H : ℝ) (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |f y - MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f (holderOrder t) x)| ≤
      ((d : ℝ) ^ holderOrder t * H / (holderOrder t).factorial) * ‖y - x‖ ^ t := by
  have hreg := holderBall_regular f t H hf
  cases hk : holderOrder t with
  | zero =>
    rw [holderTaylorPolynomial_zero_eval]
    have hh := holderBall_coordinate_modulus f t H hH hf
      (fun i => Fin.elim0 (show Fin 0 from hk ▸ i)) y x hy hx
    rw [coordinateDerivative_of_order_zero f _ hk, coordinateDerivative_of_order_zero f _ hk] at hh
    simpa [hk, holderExponent] using hh
  | succ n =>
    have hft : ContDiffOn ℝ (n + 1) f (cube d) := by simpa [hk] using hreg.2
    let F : ℝ → ℝ := f ∘ linePath x y
    have hF : ContDiffOn ℝ (n + 1) F (Icc (0 : ℝ) 1) := linePath_contDiffOn f hft x y hx hy
    have hn : (n : WithTop ℕ∞) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self n
    have hd := hF.differentiableOn_iteratedDerivWithin hn
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    obtain ⟨z, hz, hrem⟩ := taylor_mean_remainder_lagrange (f := F) (n := n)
      (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (by norm_num)
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hF.of_succ)
      (by simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hd.mono Ioo_subset_Icc_self)
    have hz' : z ∈ Icc (0 : ℝ) 1 := by
      have hzo : z ∈ Ioo (0 : ℝ) 1 := by
        simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hz
      exact ⟨hzo.1.le, hzo.2.le⟩
    have hzCube := linePath_mem_cube x y hx hy z hz'
    have hD := holderBall_iteratedFDerivWithin_modulus f t H hH hf (linePath x y z) x hzCube hx
    rw [hk] at hD
    have hD' : ‖iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) -
        iteratedFDerivWithin ℝ (n + 1) f (cube d) x‖ ≤
        (d : ℝ) ^ (n + 1) * H * ‖y - x‖ ^ holderExponent t := by
      apply hD.trans
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (linePath_sub_base_norm_le x y z hz')
          (holderExponent_pos hreg.1).le) (by positivity)
    have hDD : |iteratedDerivWithin (n + 1) F (Icc (0 : ℝ) 1) z -
        iteratedDerivWithin (n + 1) F (Icc (0 : ℝ) 1) 0| ≤
        (d : ℝ) ^ (n + 1) * H * ‖y - x‖ ^ holderExponent t * ‖y - x‖ ^ (n + 1) := by
      rw [linePath_iteratedDerivWithin f hft le_rfl x y hx hy z hz',
        linePath_iteratedDerivWithin f hft le_rfl x y hx hy 0 (by constructor <;> norm_num),
        linePath_zero, ← Real.norm_eq_abs]
      have hb := (iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) -
        iteratedFDerivWithin ℝ (n + 1) f (cube d) x).le_opNorm (fun _ => y - x)
      have hb' : ‖iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) (fun _ => y - x) -
          iteratedFDerivWithin ℝ (n + 1) f (cube d) x (fun _ => y - x)‖ ≤
          ‖iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) -
            iteratedFDerivWithin ℝ (n + 1) f (cube d) x‖ * ‖y - x‖ ^ (n + 1) := by
        simpa only [sub_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hb
      exact hb'.trans
        (mul_le_mul_of_nonneg_right hD' (by positivity))
    have hTaylor := linePath_taylor_eq f hft x y hx hy
    have herror : f y - MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f (n + 1) x) =
        (iteratedDerivWithin (n + 1) F (Icc (0 : ℝ) 1) z -
          iteratedDerivWithin (n + 1) F (Icc (0 : ℝ) 1) 0) / (n + 1).factorial := by
      rw [← hTaylor, taylorWithinEval_succ]
      have hr : F 1 - taylorWithinEval F n (Icc (0 : ℝ) 1) 0 1 =
          iteratedDerivWithin (n + 1) F (Icc (0 : ℝ) 1) z / (n + 1).factorial := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), sub_zero, one_pow, mul_one] using hrem
      have hf1 : F 1 = f y := by simp [F]
      rw [hf1] at hr
      simp only [sub_zero, one_pow, mul_one, smul_eq_mul]
      rw [Nat.factorial_succ]
      push_cast
      dsimp [F] at hr ⊢
      rw [Nat.factorial_succ] at hr
      push_cast at hr
      linear_combination hr
    rw [herror, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ↑(n + 1).factorial)]
    apply (div_le_div_of_nonneg_right hDD (by positivity)).trans_eq
    have he : holderExponent t + (n + 1 : ℕ) = t := by
      simp only [holderExponent, hk]
      ring
    have hepow : ‖y - x‖ ^ holderExponent t * ‖y - x‖ ^ (n + 1) = ‖y - x‖ ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_add_of_nonneg (norm_nonneg _)
        (holderExponent_pos hreg.1).le (by positivity), he]
    calc
      _ = ((d : ℝ) ^ (n + 1) * H / (n + 1).factorial) *
          (‖y - x‖ ^ holderExponent t * ‖y - x‖ ^ (n + 1)) := by ring
      _ = _ := by rw [hepow]

end RoughRegime.Model
