module

public import NearlyMinimax.HighAffineMixedPartials
public import NearlyMinimax.HighFrameLegality


@[expose] public section

/-! Actual original mixed-partial bounds and active-label counts for the
periodized field in the literal intrinsic coefficient ball. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem highPeriodizedChart_multiPartial_intrinsic_bound {d : ℕ}
    (C : ModelConstants d) (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (P : MvPolynomial (Fin d) ℝ)
    (hP : frameCoefficientL1 P ≤ (highIntrinsicFrameConstant C)⁻¹)
    (γ : Fin d → Fin (C.order+1)) (hγ : (∑ r, (γ r).val) ≤ C.order)
    (x : Covariate d) :
    |multiPartial (highPeriodizedChart d k j (highFrameProfile P))
      (fun r => (γ r).val) x| ≤ (k : ℝ) ^ (∑ r, (γ r).val) := by
  obtain ⟨z,hz,he⟩ := highPeriodizedChart_multiPartial_local d k hk j P
    (fun r => (γ r).val) x
  rw [he,abs_mul,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg k) _)]
  have h := mul_le_mul_of_nonneg_left
    (highFrameProfile_intrinsic_ball_derivative C P hP γ hγ
      (fun r => (k : ℝ)*x r-z r)) (pow_nonneg (Nat.cast_nonneg k) (∑ r, (γ r).val))
  simpa only [mul_one] using h

 theorem highPeriodizedChart_multiPartial_overlap (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ)
    (γ : Fin d → ℕ) (x : Covariate d) :
    (Finset.univ.filter (fun j =>
      multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ x ≠ 0)).card ≤
      2 ^ d := by
  have hs : Finset.univ.filter (fun j =>
      multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ x ≠ 0) ⊆
    Finset.univ.filter (fun j => iteratedFDeriv ℝ (∑ r, γ r)
      (highPeriodizedChart d k j (highFrameProfile (P j))) x ≠ 0) := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hz
    have hn := (Finset.mem_filter.mp hj).2
    apply hn
    rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
      ((highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
        (highFrameProfile_zero_of_window_zero (P j))).of_le (by simp)).contDiffOn
      γ le_rfl x (mem_univ x),hz]
    simp
  exact (Finset.card_le_card hs).trans
    (highPeriodizedChart_derivative_overlap d k hk (fun j => highFrameProfile (P j))
      (fun j => highFrameProfile_zero_of_window_zero (P j)) (∑ r, γ r) x)

 theorem highPeriodizedChart_multiPartial_difference_overlap (d k : ℕ) [NeZero k]
    (hk : 4 ≤ k) (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ)
    (γ : Fin d → ℕ) (x y : Covariate d) :
    (Finset.univ.filter (fun j =>
      multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ x -
      multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ y ≠ 0)).card ≤
      2 ^ (d+1) := by
  let A := Finset.univ.filter (fun j =>
    multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ x ≠ 0)
  let B := Finset.univ.filter (fun j =>
    multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ y ≠ 0)
  have hs : Finset.univ.filter (fun j =>
      multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ x -
      multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ y ≠ 0) ⊆ A ∪ B := by
    intro j hj
    have hn := (Finset.mem_filter.mp hj).2
    by_cases hx : multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ x ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro hy
      exact hn (by rw [not_ne_iff.mp hx,hy]; simp)
  have hx := highPeriodizedChart_multiPartial_overlap d k hk P γ x
  have hy := highPeriodizedChart_multiPartial_overlap d k hk P γ y
  have h := (Finset.card_le_card hs).trans ((Finset.card_union_le A B).trans
    (Nat.add_le_add hx hy))
  convert h using 1 <;> simp [Nat.pow_succ, Nat.mul_two]

 theorem highFrameField_multiPartial_sum (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ)
    (γ : Fin d → ℕ) (x : Covariate d) :
    multiPartial (highFrameField d k η P) γ x = η *
      ∑ j, multiPartial (highPeriodizedChart d k j (highFrameProfile (P j))) γ x := by
  have he : highFrameField d k η P = fun y =>
      ∑ j, η • highPeriodizedChart d k j (highFrameProfile (P j)) y := by
    funext y
    simp only [highFrameField,smul_eq_mul,Finset.mul_sum]
  rw [he]
  simpa only [smul_eq_mul,Finset.mul_sum] using multiPartial_sum_smul Finset.univ
    (fun j => highPeriodizedChart d k j (highFrameProfile (P j)))
    (fun j _ => highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
      (highFrameProfile_zero_of_window_zero (P j))) (fun _ => η) γ x

 theorem highFrameField_multiPartial_intrinsic_bound {d : ℕ}
    (C : ModelConstants d) (k : ℕ) [NeZero k] (hk : 4 ≤ k) (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ)
    (hP : ∀ j, frameCoefficientL1 (P j) ≤ (highIntrinsicFrameConstant C)⁻¹)
    (γ : Fin d → Fin (C.order+1)) (hγ : (∑ r, (γ r).val) ≤ C.order)
    (x : Covariate d) :
    |multiPartial (highFrameField d k η P) (fun r => (γ r).val) x| ≤
      |η| * (2 : ℝ)^d * (k : ℝ)^(∑ r, (γ r).val) := by
  rw [highFrameField_multiPartial_sum,abs_mul]
  have hs := finite_sum_norm_le_active_count
    (fun j => multiPartial (highPeriodizedChart d k j (highFrameProfile (P j)))
      (fun r => (γ r).val) x) (2^d) ((k : ℝ)^(∑ r, (γ r).val))
    (pow_nonneg (Nat.cast_nonneg k) _)
    (fun j => by simpa only [Real.norm_eq_abs] using
      highPeriodizedChart_multiPartial_intrinsic_bound C k hk j (P j) (hP j) γ hγ x)
    (highPeriodizedChart_multiPartial_overlap d k hk P (fun r => (γ r).val) x)
  have h := mul_le_mul_of_nonneg_left hs (abs_nonneg η)
  push_cast at h
  simpa only [Real.norm_eq_abs,mul_assoc] using h

end NearlyMinimax
