module

public import NearlyMinimax.HighIntrinsicPeriodizedHolder


@[expose] public section

/-! Exact manuscript C_w legality for the actual periodized polynomial field
in the literal intrinsic frame coefficient ball. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem highFrameField_intrinsic_top_modulus {d : ℕ} (C : ModelConstants d)
    (k : ℕ) [NeZero k] (hk : 4 ≤ k) (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ)
    (hP : ∀ j, frameCoefficientL1 (P j) ≤ (highIntrinsicFrameConstant C)⁻¹)
    (γ : Fin d → Fin (C.order+1)) (hγ : (∑ r, (γ r).val) = C.order)
    (x y : Covariate d) :
    |multiPartial (highFrameField d k η P) (fun r => (γ r).val) x -
      multiPartial (highFrameField d k η P) (fun r => (γ r).val) y| ≤
      |η| * (2 : ℝ)^(d+1) * (k : ℝ)^C.order *
        ((k : ℝ)*euclideanNorm (x-y))^C.alpha := by
  rw [highFrameField_multiPartial_sum,highFrameField_multiPartial_sum,
    ← mul_sub,abs_mul,← Finset.sum_sub_distrib]
  have hs := finite_sum_norm_le_active_count
    (fun j => multiPartial (highPeriodizedChart d k j (highFrameProfile (P j)))
      (fun r => (γ r).val) x -
      multiPartial (highPeriodizedChart d k j (highFrameProfile (P j)))
      (fun r => (γ r).val) y) (2^(d+1))
    ((k : ℝ)^C.order*((k : ℝ)*euclideanNorm (x-y))^C.alpha)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg k) _)
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg _)) _))
    (fun j => by simpa only [Real.norm_eq_abs] using
      highPeriodizedChart_intrinsic_top_modulus C k hk j (P j) (hP j) γ hγ x y)
    (highPeriodizedChart_multiPartial_difference_overlap d k hk P (fun r => (γ r).val) x y)
  have h := mul_le_mul_of_nonneg_left hs (abs_nonneg η)
  push_cast at h
  simpa only [Real.norm_eq_abs,mul_assoc] using h

/-- With the intrinsic Cfr itself, the full original mixed-partial norm has
exactly C_w=2^d(choose(d+ell,d)+2), uniformly in degree, resolution and domain. -/
 theorem highFrameField_intrinsic_original_model_bounds {d : ℕ} (C : ModelConstants d)
    (k : ℕ) [NeZero k] (hk : 4 ≤ k) (cf : ℝ) (hcf : 0 ≤ cf)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ)
    (hP : ∀ j, frameCoefficientL1 (P j) ≤ (highIntrinsicFrameConstant C)⁻¹) :
    let F := highFrameField d k (cf * (k : ℝ)^(-C.smoothness)) P
    (∀ x, |F x| ≤ (2 : ℝ)^d*(cf*(k : ℝ)^(-C.smoothness))) ∧
    (∀ γ : Fin d → Fin (C.order+1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
      |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ)^d*cf) ∧
    (∀ γ : Fin d → Fin (C.order+1), (∑ r, (γ r).val) = C.order → ∀ x y,
      |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        (2*((2 : ℝ)^d*cf))*euclideanNorm (x-y)^C.alpha) ∧
    (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
      ENNReal.ofReal (highWindowHolderConstant C*cf)) := by
  let F := highFrameField d k (cf*(k : ℝ)^(-C.smoothness)) P
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hkR
  have heta : 0 ≤ cf*(k : ℝ)^(-C.smoothness) := by positivity
  have hs : ∀ γ : Fin d → Fin (C.order+1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
      |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ)^d*cf := by
    intro γ hγ x
    have h := highFrameField_multiPartial_intrinsic_bound C k hk
      (cf*(k : ℝ)^(-C.smoothness)) P hP γ hγ x
    rw [abs_of_nonneg heta] at h
    have hpow : (k : ℝ)^(-C.smoothness)*(k : ℝ)^(∑ r, (γ r).val) ≤ 1 := by
      rw [← Real.rpow_natCast,← Real.rpow_add hkpos]
      apply Real.rpow_le_one_of_one_le_of_nonpos hkR
      have hγR : (((∑ r, (γ r).val) : ℕ) : ℝ) ≤ C.order := by exact_mod_cast hγ
      linarith [C.order_lt]
    calc
      _ ≤ (cf*(k : ℝ)^(-C.smoothness))*(2 : ℝ)^d*(k : ℝ)^(∑ r, (γ r).val) := h
      _ = ((2 : ℝ)^d*cf)*((k : ℝ)^(-C.smoothness)*(k : ℝ)^(∑ r, (γ r).val)) := by ring
      _ ≤ ((2 : ℝ)^d*cf)*1 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := mul_one _
  have hm : ∀ γ : Fin d → Fin (C.order+1), (∑ r, (γ r).val) = C.order → ∀ x y,
      |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        (2*((2 : ℝ)^d*cf))*euclideanNorm (x-y)^C.alpha := by
    intro γ hγ x y
    have h := highFrameField_intrinsic_top_modulus C k hk
      (cf*(k : ℝ)^(-C.smoothness)) P hP γ hγ x y
    rw [abs_of_nonneg heta,Real.mul_rpow (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)
      (show 0 ≤ euclideanNorm (x-y) from Real.sqrt_nonneg _)] at h
    have he : (k : ℝ)^(-C.smoothness)*(k : ℝ)^C.order*(k : ℝ)^C.alpha = 1 := by
      rw [← Real.rpow_natCast,← Real.rpow_add hkpos,← Real.rpow_add hkpos]
      have hh : -C.smoothness+(C.order : ℝ)+C.alpha = 0 := by
        unfold ModelConstants.alpha
        ring
      rw [hh,Real.rpow_zero]
    have he2 : (cf*(k : ℝ)^(-C.smoothness))*(2 : ℝ)^(d+1)*(k : ℝ)^C.order*
        ((k : ℝ)^C.alpha*euclideanNorm (x-y)^C.alpha) =
      (2*((2 : ℝ)^d*cf))*euclideanNorm (x-y)^C.alpha := by
      calc
        _ = ((2 : ℝ)^(d+1)*cf)*((k : ℝ)^(-C.smoothness)*(k : ℝ)^C.order*
            (k : ℝ)^C.alpha)*euclideanNorm (x-y)^C.alpha := by ring
        _ = _ := by rw [he,pow_succ]; ring
    exact h.trans_eq he2
  have hv (x : Covariate d) : |F x| ≤ (2 : ℝ)^d*(cf*(k : ℝ)^(-C.smoothness)) := by
    have h := highFrameField_multiPartial_intrinsic_bound C k hk
      (cf*(k : ℝ)^(-C.smoothness)) P hP (fun _ => (0 : Fin (C.order+1))) (by simp) x
    simp only [Fin.val_zero,Finset.sum_const_zero,multiPartial_zero_index,pow_zero,mul_one,
      abs_of_nonneg heta] at h
    exact h.trans_eq (mul_comm _ _)
  refine ⟨hv,hs,hm,?_⟩
  intro U
  have h := holderNorm_of_global_mixed_bounds_binomial U F C.order C.alpha
    ((2 : ℝ)^d*cf) (2*((2 : ℝ)^d*cf)) (by positivity) (by positivity) hs hm
  convert h using 1
  congr 1
  unfold highWindowHolderConstant
  ring

end NearlyMinimax
