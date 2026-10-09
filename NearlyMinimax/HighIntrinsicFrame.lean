module

public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.ModelRegularity


@[expose] public section

/-! The intrinsic frame normalization used in the manuscript: the maximum
of one and the supremum of the original C^s norms of individual compact
windowed monomials. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

theorem multiPartial_sum_smul {d : ℕ} {I : Type*} (s : Finset I)
    (F : I → Covariate d → ℝ) (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i))
    (c : I → ℝ) (γ : Fin d → ℕ) (x : Covariate d) :
    multiPartial (fun y => ∑ i ∈ s, c i • F i y) γ x =
      ∑ i ∈ s, c i • multiPartial (F i) γ x := by
  have hs : ∀ i ∈ s, ContDiff ℝ ∞ (fun y => c i • F i y) :=
    fun i hi => (hF i hi).const_smul (c i)
  have hall : ContDiff ℝ ∞ (fun y => ∑ i ∈ s, c i • F i y) := ContDiff.sum hs
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
    (hall.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x),
    iteratedFDeriv_fun_sum_apply (fun i hi => ((hs i hi).of_le (by simp)).contDiffAt)]
  simp only [ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_const_smul_apply' (((hF i hi).of_le (by simp)).contDiffAt),
    ContinuousMultilinearMap.smul_apply,
    multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
      ((hF i hi).of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x)]

private theorem derivativeSup_sum_smul_le {d : ℕ} {I : Type*} (s : Finset I)
    (U : Set (Covariate d)) (F : I → Covariate d → ℝ) (c : I → ℝ) :
    derivativeSup U (fun x => ∑ i ∈ s, c i • F i x) ≤
      ∑ i ∈ s, ENNReal.ofReal |c i| * derivativeSup U (F i) := by
  apply iSup_le
  intro x
  calc
    ENNReal.ofReal |∑ i ∈ s, c i • F i x| ≤
        ENNReal.ofReal (∑ i ∈ s, |c i| * |F i x|) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.norm_eq_abs, smul_eq_mul, abs_mul] using norm_sum_le s (fun i => c i • F i x)
    _ = ∑ i ∈ s, ENNReal.ofReal |c i| * ENNReal.ofReal |F i x| := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      simp only [ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact le_iSup (fun z : U => ENNReal.ofReal |F i z|) x

private theorem holderSeminorm_sum_smul_le {d : ℕ} {I : Type*} (s : Finset I)
    (U : Set (Covariate d)) (F : I → Covariate d → ℝ) (c : I → ℝ) (α : ℝ) :
    holderSeminorm U (fun x => ∑ i ∈ s, c i • F i x) α ≤
      ∑ i ∈ s, ENNReal.ofReal |c i| * holderSeminorm U (F i) α := by
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  by_cases hxy : (x : Covariate d) = y
  · simp only [if_pos hxy]
    exact bot_le
  simp only [if_neg hxy]
  have hden : 0 < euclideanNorm (x.val - y.val) ^ α :=
    Real.rpow_pos_of_pos (euclideanNorm_pos_of_ne_zero _ (sub_ne_zero.mpr hxy)) α
  calc
    ENNReal.ofReal (|∑ i ∈ s, c i • F i x - ∑ i ∈ s, c i • F i y| /
        euclideanNorm (x.val - y.val) ^ α) ≤
      ENNReal.ofReal (∑ i ∈ s, |c i| * (|F i x - F i y| /
        euclideanNorm (x.val - y.val) ^ α)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.sum_sub_distrib]
      simp_rw [← smul_sub]
      have hn := norm_sum_le s (fun i => c i • (F i x - F i y))
      simp only [Real.norm_eq_abs, smul_eq_mul, abs_mul] at hn
      have hh := div_le_div_of_nonneg_right hn hden.le
      simpa only [Finset.sum_div, mul_div_assoc, smul_eq_mul] using hh
    _ = ∑ i ∈ s, ENNReal.ofReal |c i| * ENNReal.ofReal
        (|F i x - F i y| / euclideanNorm (x.val - y.val) ^ α) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (abs_nonneg _)
        (div_nonneg (abs_nonneg _) hden.le))]
      simp only [ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact le_iSup_of_le x (le_iSup_of_le y (by simp only [if_neg hxy]; exact le_rfl))

/-- The original sum/max mixed-partial norm is subadditive for a genuine
finite linear combination of smooth functions. -/
theorem holderNorm_sum_smul_le {d : ℕ} {I : Type*} (s : Finset I)
    (U : Set (Covariate d)) (F : I → Covariate d → ℝ)
    (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i)) (c : I → ℝ) (ℓ : ℕ) (α : ℝ) :
    holderNorm U (fun x => ∑ i ∈ s, c i • F i x) ℓ α ≤
      ∑ i ∈ s, ENNReal.ofReal |c i| * holderNorm U (F i) ℓ α := by
  have hpart (γ : Fin d → ℕ) :
      multiPartial (fun x => ∑ i ∈ s, c i • F i x) γ =
        fun x => ∑ i ∈ s, c i • multiPartial (F i) γ x := by
    funext x
    exact multiPartial_sum_smul s F hF c γ x
  let D (i : I) (γ : Fin d → Fin (ℓ+1)) : ℝ≥0∞ :=
    if (∑ r, (γ r).val) ≤ ℓ then derivativeSup U (multiPartial (F i) (fun r => (γ r).val)) else 0
  let H (i : I) : ℝ≥0∞ := ⨆ γ : Fin d → Fin (ℓ+1),
    if (∑ r, (γ r).val) = ℓ then holderSeminorm U (multiPartial (F i) (fun r => (γ r).val)) α else 0
  have hd : (∑ γ : Fin d → Fin (ℓ+1), if (∑ r, (γ r).val) ≤ ℓ then
      derivativeSup U (multiPartial (fun x => ∑ i ∈ s, c i • F i x) (fun r => (γ r).val)) else 0) ≤
      ∑ i ∈ s, ENNReal.ofReal |c i| * ∑ γ, D i γ := by
    calc
      _ ≤ ∑ γ : Fin d → Fin (ℓ+1), ∑ i ∈ s, ENNReal.ofReal |c i| * D i γ := by
        apply Finset.sum_le_sum
        intro γ hγ
        by_cases horder : (∑ r, (γ r).val) ≤ ℓ
        · simp only [if_pos horder, D]
          rw [hpart]
          exact derivativeSup_sum_smul_le s U _ c
        · simp only [if_neg horder, D, mul_zero, Finset.sum_const_zero, le_refl]
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have hh : (⨆ γ : Fin d → Fin (ℓ+1), if (∑ r, (γ r).val) = ℓ then
      holderSeminorm U (multiPartial (fun x => ∑ i ∈ s, c i • F i x) (fun r => (γ r).val)) α else 0) ≤
      ∑ i ∈ s, ENNReal.ofReal |c i| * H i := by
    apply iSup_le
    intro γ
    by_cases horder : (∑ r, (γ r).val) = ℓ
    · simp only [if_pos horder]
      rw [hpart]
      apply (holderSeminorm_sum_smul_le s U _ c α).trans
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact le_iSup_of_le γ (by simp only [if_pos horder]; exact le_rfl)
    · simp only [if_neg horder]
      exact bot_le
  apply (add_le_add hd hh).trans_eq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_add]
  rfl

/-- The original C^s norm of one windowed scaled monomial, with no degree
cutoff. -/
def highIntrinsicProfileNorm {d : ℕ} (C : ModelConstants d) (β : Fin d →₀ ℕ) : ℝ≥0∞ :=
  holderNorm univ (highFrameProfile (MvPolynomial.monomial β (1 : ℝ))) C.order C.alpha

/-- The literal degree-independent frame constant in the paper. -/
def highIntrinsicFrameConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  max 1 (sSup (Set.range (fun β : Fin d →₀ ℕ => (highIntrinsicProfileNorm C β).toReal)))

theorem frameCoefficientL1_monomial_one {d : ℕ} (β : Fin d →₀ ℕ) :
    frameCoefficientL1 (MvPolynomial.monomial β (1 : ℝ)) = 1 := by
  classical
  simp [frameCoefficientL1, MvPolynomial.support_monomial]

theorem highIntrinsicProfileNorm_uniform_bound {d : ℕ} (C : ModelConstants d) :
    ∃ K : ℝ, 0 < K ∧ ∀ β, highIntrinsicProfileNorm C β ≤ ENNReal.ofReal K := by
  obtain ⟨K, hK, hbound⟩ := highFrameProfile_holderNorm_bound C
  refine ⟨K, hK, fun β => ?_⟩
  simpa only [highIntrinsicProfileNorm, frameCoefficientL1_monomial_one, mul_one]
    using hbound (MvPolynomial.monomial β (1 : ℝ)) univ

theorem highIntrinsicProfileNorm_ne_top {d : ℕ} (C : ModelConstants d) (β : Fin d →₀ ℕ) :
    highIntrinsicProfileNorm C β ≠ ⊤ := by
  obtain ⟨K, _, hbound⟩ := highIntrinsicProfileNorm_uniform_bound C
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound β)

theorem highIntrinsicFrameConstant_ge_one {d : ℕ} (C : ModelConstants d) :
    1 ≤ highIntrinsicFrameConstant C := le_max_left _ _

theorem highIntrinsicFrameConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < highIntrinsicFrameConstant C := lt_of_lt_of_le (by norm_num) (highIntrinsicFrameConstant_ge_one C)

/-- The defining supremum is bounded uniformly over all multi-indices. -/
theorem highIntrinsicFrameConstant_uniform_bound {d : ℕ} (C : ModelConstants d) :
    ∃ K : ℝ, 0 < K ∧ highIntrinsicFrameConstant C ≤ max 1 K := by
  obtain ⟨K, hK, hbound⟩ := highIntrinsicProfileNorm_uniform_bound C
  refine ⟨K, hK, max_le (le_max_left _ _) ?_⟩
  apply (csSup_le (Set.range_nonempty _ ) ?_).trans (le_max_right _ _)
  rintro _ ⟨β, rfl⟩
  have ht := (ENNReal.toReal_le_toReal (highIntrinsicProfileNorm_ne_top C β)
    ENNReal.ofReal_ne_top).mpr (hbound β)
  simpa only [ENNReal.toReal_ofReal hK.le] using ht

theorem highIntrinsicProfileNorm_le_constant {d : ℕ} (C : ModelConstants d) (β : Fin d →₀ ℕ) :
    highIntrinsicProfileNorm C β ≤ ENNReal.ofReal (highIntrinsicFrameConstant C) := by
  obtain ⟨K, hK, hbound⟩ := highIntrinsicProfileNorm_uniform_bound C
  have hb : BddAbove (Set.range (fun β : Fin d →₀ ℕ => (highIntrinsicProfileNorm C β).toReal)) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨β, rfl⟩
    have ht := (ENNReal.toReal_le_toReal (highIntrinsicProfileNorm_ne_top C β)
      ENNReal.ofReal_ne_top).mpr (hbound β)
    simpa only [ENNReal.toReal_ofReal hK.le] using ht
  have hs : (highIntrinsicProfileNorm C β).toReal ≤ highIntrinsicFrameConstant C :=
    (le_csSup hb (Set.mem_range_self β)).trans (le_max_right _ _)
  calc
    _ = ENNReal.ofReal (highIntrinsicProfileNorm C β).toReal :=
      (ENNReal.ofReal_toReal (highIntrinsicProfileNorm_ne_top C β)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hs

theorem highFrameProfile_as_sum_monomials {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    highFrameProfile P = fun x => ∑ β ∈ P.support,
      P.coeff β • highFrameProfile (MvPolynomial.monomial β (1 : ℝ)) x := by
  funext x
  simp only [highFrameProfile, frameScaledPolynomial_eval, smul_eq_mul]
  change highWindowTensor d x * MvPolynomial.eval₂ (RingHom.id ℝ) (fun r => x r / 8) P = _
  rw [MvPolynomial.eval₂_eq']
  simp only [MvPolynomial.eval_monomial, one_mul, RingHom.id_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [Finsupp.prod_fintype _ _ (fun r => by simp)]
  ring

/-- Every coefficient vector in the paper's exact intrinsic ball has a
profile with original global C^s norm at most one. -/
theorem highFrameProfile_intrinsic_ball_norm {d : ℕ} (C : ModelConstants d)
    (P : MvPolynomial (Fin d) ℝ)
    (hP : frameCoefficientL1 P ≤ (highIntrinsicFrameConstant C)⁻¹) :
    holderNorm univ (highFrameProfile P) C.order C.alpha ≤ 1 := by
  rw [highFrameProfile_as_sum_monomials P]
  apply (holderNorm_sum_smul_le P.support univ
    (fun β => highFrameProfile (MvPolynomial.monomial β (1 : ℝ)))
    (fun β _ => highFrameProfile_contDiff _) P.coeff C.order C.alpha).trans
  calc
    _ ≤ ∑ β ∈ P.support, ENNReal.ofReal |P.coeff β| *
        ENNReal.ofReal (highIntrinsicFrameConstant C) := by
      apply Finset.sum_le_sum
      intro β hβ
      gcongr
      exact highIntrinsicProfileNorm_le_constant C β
    _ = ENNReal.ofReal (frameCoefficientL1 P * highIntrinsicFrameConstant C) := by
      symm
      unfold frameCoefficientL1
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
        (fun β hβ => mul_nonneg (abs_nonneg _) (highIntrinsicFrameConstant_pos C).le)]
      simp only [ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ 1 := by
      apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hP
        (highIntrinsicFrameConstant_pos C).le)).trans_eq
      rw [inv_mul_cancel₀ (highIntrinsicFrameConstant_pos C).ne', ENNReal.ofReal_one]

theorem highFrameProfile_intrinsic_ball_derivative {d : ℕ} (C : ModelConstants d)
    (P : MvPolynomial (Fin d) ℝ)
    (hP : frameCoefficientL1 P ≤ (highIntrinsicFrameConstant C)⁻¹)
    (γ : Fin d → Fin (C.order+1)) (hγ : (∑ r, (γ r).val) ≤ C.order) (x : Covariate d) :
    |multiPartial (highFrameProfile P) (fun r => (γ r).val) x| ≤ 1 := by
  apply holderNorm_derivative_bound univ _ C.order C.alpha 1 (by norm_num)
    _ γ hγ x (mem_univ x)
  simpa only [ENNReal.ofReal_one] using highFrameProfile_intrinsic_ball_norm C P hP

theorem highFrameProfile_intrinsic_ball_modulus {d : ℕ} (C : ModelConstants d)
    (P : MvPolynomial (Fin d) ℝ)
    (hP : frameCoefficientL1 P ≤ (highIntrinsicFrameConstant C)⁻¹)
    (γ : Fin d → Fin (C.order+1)) (hγ : (∑ r, (γ r).val) = C.order) (x y : Covariate d) :
    |multiPartial (highFrameProfile P) (fun r => (γ r).val) x -
      multiPartial (highFrameProfile P) (fun r => (γ r).val) y| ≤
      euclideanNorm (x-y) ^ C.alpha := by
  have h := holderNorm_top_derivative_modulus univ _ C.order C.alpha 1 (by norm_num)
    (by simpa only [ENNReal.ofReal_one] using highFrameProfile_intrinsic_ball_norm C P hP)
    γ hγ x y (mem_univ x) (mem_univ y)
  simpa only [one_mul] using h

/-- All genuine mixed partials retain the compact support of the window. -/
theorem highFrameProfile_multiPartial_support_bound {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (γ : Fin d → ℕ) (x : Covariate d) (hx : multiPartial (highFrameProfile P) γ x ≠ 0) :
    ∀ r, |x r| ≤ 3 / 4 := by
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
    ((highFrameProfile_contDiff P).of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x)] at hx
  have hn : iteratedFDeriv ℝ (∑ r, γ r) (highFrameProfile P) x ≠ 0 := by
    intro hz
    exact hx (by rw [hz]; simp)
  have ht : x ∈ tsupport (highFrameProfile P) :=
    support_iteratedFDeriv_subset (𝕜 := ℝ) (∑ r, γ r) hn
  exact highWindowTensor_tsupport_bound (highFrameProfile_tsupport_subset P ht)

/-- Literal finite frame coefficient ball from the manuscript. -/
theorem highFrameCoefficientProfile_intrinsic_ball_norm {d D : ℕ} (C : ModelConstants d)
    (c : HighFrameIndex d D → ℝ) (hc : (∑ γ, |c γ|) ≤ (highIntrinsicFrameConstant C)⁻¹) :
    holderNorm univ (highFrameProfile (highFramePolynomial c)) C.order C.alpha ≤ 1 :=
  highFrameProfile_intrinsic_ball_norm C _ ((highFramePolynomial_coefficientL1_le c).trans hc)

theorem highFrameProfile_intrinsic_ball_value {d : ℕ} (C : ModelConstants d)
    (P : MvPolynomial (Fin d) ℝ)
    (hP : frameCoefficientL1 P ≤ (highIntrinsicFrameConstant C)⁻¹) (x : Covariate d) :
    |highFrameProfile P x| ≤ 1 := by
  have h := highFrameProfile_intrinsic_ball_derivative C P hP
    (fun _ => (0 : Fin (C.order+1))) (by simp) x
  have hz : (List.finRange d).flatMap (fun _ : Fin d => ([] : List (Fin d))) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  simpa only [Fin.val_zero, multiPartial, List.replicate_zero, hz, List.foldl_nil] using h

end NearlyMinimax
