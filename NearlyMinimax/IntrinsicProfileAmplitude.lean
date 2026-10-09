module

public import NearlyMinimax.HighIntrinsicFrame


@[expose] public section

/-! The global C^s norm includes both the top derivative supremum and its
Hölder seminorm.  Compact support therefore gives the sharper one-half
amplitude useful for periodizing a profile across separated chart copies. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private theorem euclideanNorm_single {d : ℕ} (i : Fin d) (a : ℝ) :
    euclideanNorm (Pi.single i a) = |a| := by
  simp [euclideanNorm, Pi.single_apply, Real.sqrt_sq_eq_abs]

/-- A point where a compactly supported function vanishes can be chosen
at exactly unit Euclidean distance from any given point. -/
theorem compactCube_zero_at_unit_distance {d : ℕ} (hd : 0 < d)
    (G : Covariate d → ℝ) (hG : ∀ x, G x ≠ 0 → ∀ i, |x i| ≤ 3 / 4)
    (x : Covariate d) : ∃ y, G y = 0 ∧ x ≠ y ∧ euclideanNorm (x-y) = 1 := by
  let i : Fin d := ⟨0, hd⟩
  let a : ℝ := if 0 ≤ x i then 1 else -1
  let y : Covariate d := x + Pi.single i a
  have ha : |a| = 1 := by dsimp [a]; split_ifs <;> norm_num
  have habs : 1 ≤ |y i| := by
    dsimp [y, a]
    simp only [Pi.add_apply, Pi.single_eq_same]
    split_ifs with hx
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_neg (by linarith)]
      linarith
  have hzero : G y = 0 := by
    by_contra hn
    have hb := hG y hn i
    linarith
  have hdiff : x-y = Pi.single i (-a) := by
    dsimp [y]
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
    ext r
    simp only [Pi.single_apply, Pi.neg_apply]
    split_ifs <;> simp
  have hdist : euclideanNorm (x-y) = 1 := by rw [hdiff, euclideanNorm_single, abs_neg, ha]
  refine ⟨y, hzero, ?_, hdist⟩
  intro hxy
  have hz : euclideanNorm (x-y) = 0 := by simp [hxy, euclideanNorm]
  linarith

/-- Every top-order mixed partial of a profile in the literal intrinsic
frame ball has amplitude at most one half. -/
theorem highFrameProfile_intrinsic_top_amplitude {d : ℕ} (C : ModelConstants d)
    (P : MvPolynomial (Fin d) ℝ)
    (hP : frameCoefficientL1 P ≤ (highIntrinsicFrameConstant C)⁻¹)
    (γ : Fin d → Fin (C.order+1)) (hγ : (∑ r, (γ r).val) = C.order)
    (x : Covariate d) :
    |multiPartial (highFrameProfile P) (fun r => (γ r).val) x| ≤ 1 / 2 := by
  let G : Covariate d → ℝ := multiPartial (highFrameProfile P) (fun r => (γ r).val)
  obtain ⟨y, hy, hxy, hdist⟩ := compactCube_zero_at_unit_distance C.dimension_pos G
    (fun x hx => highFrameProfile_multiPartial_support_bound P _ x hx) x
  have hd : ENNReal.ofReal |G x| ≤
      ∑ δ : Fin d → Fin (C.order+1), if (∑ r, (δ r).val) ≤ C.order then
        derivativeSup univ (multiPartial (highFrameProfile P) (fun r => (δ r).val)) else 0 := by
    apply le_trans (le_iSup (fun z : (univ : Set (Covariate d)) => ENNReal.ofReal |G z|)
      ⟨x, mem_univ x⟩)
    have hsingle := Finset.single_le_sum (fun δ (_ : δ ∈ Finset.univ) =>
      (bot_le : (0 : ℝ≥0∞) ≤ if (∑ r, (δ r).val) ≤ C.order then
        derivativeSup univ (multiPartial (highFrameProfile P) (fun r => (δ r).val)) else 0))
      (Finset.mem_univ γ)
    simpa only [if_pos hγ.le, derivativeSup, G] using hsingle
  have hh : ENNReal.ofReal |G x| ≤
      ⨆ δ : Fin d → Fin (C.order+1), if (∑ r, (δ r).val) = C.order then
        holderSeminorm univ (multiPartial (highFrameProfile P) (fun r => (δ r).val)) C.alpha else 0 := by
    apply le_iSup_of_le γ
    rw [if_pos hγ]
    unfold holderSeminorm
    apply le_iSup_of_le (⟨x, mem_univ x⟩ : (univ : Set (Covariate d)))
    apply le_iSup_of_le (⟨y, mem_univ y⟩ : (univ : Set (Covariate d)))
    simp only [if_neg hxy, G, hy, hdist, Real.one_rpow, div_one, sub_zero]
    exact le_rfl
  have htotal : ENNReal.ofReal (|G x| + |G x|) ≤ 1 := by
    rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact (add_le_add hd hh).trans (highFrameProfile_intrinsic_ball_norm C P hP)
  have hr : |G x| + |G x| ≤ (1 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
      (by simpa only [ENNReal.ofReal_one] using htotal)
  dsimp [G] at hr
  linarith

end NearlyMinimax
