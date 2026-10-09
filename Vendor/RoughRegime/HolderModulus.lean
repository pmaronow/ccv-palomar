module

public import RoughRegime.HolderGeometry


@[expose] public section

/-! A uniform spatial modulus derived from the model's actual Hölder norm. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

theorem holderBall_regular {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hf : f ∈ holderBall t H) : 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) := by
  change holderNorm f t ≤ ENNReal.ofReal H at hf
  unfold holderNorm at hf
  split_ifs at hf with hreg
  · exact hreg
  · exact False.elim (ENNReal.ofReal_ne_top (top_le_iff.mp hf))

theorem holderBall_coordinate_bound {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (q : ℕ) (hq : q ≤ holderOrder t)
    (σ : Fin q → Fin d) (x : Covariate d) (hx : x ∈ cube d) :
    |coordinateDerivative f q σ x| ≤ H := by
  have hreg := holderBall_regular f t H hf
  change holderNorm f t ≤ ENNReal.ofReal H at hf
  have hsup : derivativeSup f (holderOrder t) ≤ ENNReal.ofReal H := by
    unfold holderNorm at hf
    rw [ite_eq_left hreg] at hf
    exact le_trans le_self_add hf
  have hp : ENNReal.ofReal |coordinateDerivative f q σ x| ≤ derivativeSup f (holderOrder t) :=
    le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le σ
      (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))
  exact (ENNReal.ofReal_le_ofReal_iff hH).mp (hp.trans hsup)

theorem holderBall_coordinate_modulus {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (σ : Fin (holderOrder t) → Fin d)
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |coordinateDerivative f (holderOrder t) σ x - coordinateDerivative f (holderOrder t) σ y| ≤
      H * ‖x - y‖ ^ holderExponent t := by
  by_cases he : x = y
  · subst y
    simpa using mul_nonneg hH (Real.rpow_nonneg (norm_nonneg (x - x)) (holderExponent t))
  · have hreg := holderBall_regular f t H hf
    change holderNorm f t ≤ ENNReal.ofReal H at hf
    have hsem : holderSeminorm f t ≤ ENNReal.ofReal H := by
      unfold holderNorm at hf
      rw [ite_eq_left hreg] at hf
      exact le_trans le_add_self hf
    have hp : ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x -
        coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t) ≤
        holderSeminorm f t := le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx
      (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le he le_rfl)))))
    have hb : |coordinateDerivative f (holderOrder t) σ x -
        coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t ≤ H :=
      (ENNReal.ofReal_le_ofReal_iff hH).mp (hp.trans hsem)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr he)) _)).mp hb

lemma linear_norm_le_coordinate_bound {d : ℕ} (L : Covariate d →L[ℝ] ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hb : ∀ i, |L (EuclideanSpace.single i 1)| ≤ H) :
    ‖L‖ ≤ (d : ℝ) * H := by
  classical
  apply L.opNorm_le_bound (by positivity)
  intro x
  have hx : x = ∑ i : Fin d, x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  calc
    _ ≤ ∑ i : Fin d, ‖L (x i • EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ * H := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)
        (by simpa only [Real.norm_eq_abs] using hb i) (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * H * ‖x‖ := by simp; ring

lemma coordinateDerivative_of_order_zero {d : ℕ} (f : Covariate d → ℝ)
    (q : ℕ) (hq : q = 0) (σ : Fin q → Fin d) (x : Covariate d) :
    coordinateDerivative f q σ x = f x := by
  subst q
  rfl

theorem holderBall_spatial_modulus {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (x y : Covariate d)
    (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |f x - f y| ≤ ((d : ℝ) + 1) * H * ‖x - y‖ ^ min t 1 := by
  have hreg := holderBall_regular f t H hf
  by_cases ht : t ≤ 1
  · have hk : holderOrder t = 0 := by
      have hh : Nat.ceil t ≤ 1 := Nat.ceil_le.mpr (by simpa using ht)
      unfold holderOrder
      omega
    have hb := holderBall_coordinate_modulus f t H hH hf
      (fun i => Fin.elim0 (show Fin 0 from hk ▸ i)) x y hx hy
    have hzero : ∀ (σ : Fin (holderOrder t) → Fin d) z,
        coordinateDerivative f (holderOrder t) σ z = f z := by
      intro σ z
      exact coordinateDerivative_of_order_zero f _ hk σ z
    rw [hzero, hzero] at hb
    simp only [holderExponent, hk, min_eq_left ht, sub_zero, Nat.cast_zero] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_right
      (show H ≤ ((d : ℝ) + 1) * H by nlinarith [mul_nonneg (Nat.cast_nonneg d) hH])
      (Real.rpow_nonneg (norm_nonneg _) _))
  · have hk : 1 ≤ holderOrder t := by
      have hh : 1 < Nat.ceil t := Nat.lt_ceil.mpr (by simpa using lt_of_not_ge ht)
      unfold holderOrder
      omega
    have hdiff : DifferentiableOn ℝ f (cube d) := hreg.2.differentiableOn (by simpa using (by omega : holderOrder t ≠ 0))
    have hbound : ∀ z ∈ cube d, ‖fderivWithin ℝ f (cube d) z‖ ≤ (d : ℝ) * H := by
      intro z hz
      apply linear_norm_le_coordinate_bound _ H hH
      intro i
      have hb := holderBall_coordinate_bound f t H hH hf 1 hk (fun _ => i) z hz
      simpa only [coordinateDerivative, iteratedFDerivWithin_one_apply ((uniqueDiffOn_cube d) z hz)] using hb
    have hlip := (convex_cube d).norm_image_sub_le_of_norm_fderivWithin_le hdiff hbound hy hx
    rw [Real.norm_eq_abs] at hlip
    rw [min_eq_right (le_of_not_ge ht), Real.rpow_one]
    exact hlip.trans (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))

end RoughRegime.Model
