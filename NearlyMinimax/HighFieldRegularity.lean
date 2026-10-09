module

public import NearlyMinimax.HighSmoothnessWindows
public import NearlyMinimax.CoordinatePartialBridge
public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.AnchoredGeometry


@[expose] public section

/-! Resolution-independent derivative and Hölder estimates for actual
periodic window fields. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem finite_sum_norm_le_active_count {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] (g : J → E) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j, ‖g j‖ ≤ B)
    (hcount : (Finset.univ.filter (fun j => g j ≠ 0)).card ≤ N) :
    ‖∑ j, g j‖ ≤ (N : ℝ) * B := by
  let A := Finset.univ.filter (fun j => g j ≠ 0)
  have hsum : (∑ j, ‖g j‖) = ∑ j ∈ A, ‖g j‖ := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hg : g j = 0 <;> simp [hg]
  calc
    _ ≤ ∑ j, ‖g j‖ := norm_sum_le _ _
    _ = _ := hsum
    _ ≤ ∑ _j ∈ A, B := Finset.sum_le_sum (fun j _ => hbound j)
    _ = (A.card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB

def highWindowField (d k : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → ℝ) (x : Covariate d) : ℝ :=
  η * ∑ j, c j * highPeriodicTensor d k j x

theorem highWindowField_contDiff (d k : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → ℝ) : ContDiff ℝ ∞ (highWindowField d k η c) := by
  unfold highWindowField
  change ContDiff ℝ ∞ (fun x => η • ∑ j, c j • highPeriodicTensor d k j x)
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro j hj
  exact (highPeriodicTensor_contDiff d k j).const_smul _

theorem highWindowField_derivative_bound (d m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ η : ℝ,
      ∀ c : HighWindowLabels d k → ℝ, (∀ j, |c j| ≤ 1) →
      ∀ i ≤ m, ∀ x : Covariate d,
        ‖iteratedFDeriv ℝ i (highWindowField d k η c) x‖ ≤
          |η| * (2 : ℝ) ^ d * B * (k : ℝ) ^ i := by
  obtain ⟨B, hB0, hB⟩ := highPeriodicTensor_derivative_bound d m
  refine ⟨B, hB0, ?_⟩
  intro k hk0 hk η c hc i hi x
  letI := hk0
  have hsmooth (j : HighWindowLabels d k) : ContDiffAt ℝ i (highPeriodicTensor d k j) x :=
    ((highPeriodicTensor_contDiff d k j).of_le (by simp)).contDiffAt
  have he : iteratedFDeriv ℝ i (highWindowField d k η c) x =
      η • ∑ j, c j • iteratedFDeriv ℝ i (highPeriodicTensor d k j) x := by
    change iteratedFDeriv ℝ i
      (fun y => η • ∑ j, c j • highPeriodicTensor d k j y) x = _
    rw [iteratedFDeriv_const_smul_apply' (by
      apply ContDiffAt.sum
      intro j hj
      exact (hsmooth j).const_smul _)]
    rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hsmooth j).const_smul (c j))]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact iteratedFDeriv_const_smul_apply' (hsmooth j)
  rw [he, norm_smul, Real.norm_eq_abs]
  have hbound (j : HighWindowLabels d k) :
      ‖c j • iteratedFDeriv ℝ i (highPeriodicTensor d k j) x‖ ≤ B * (k : ℝ) ^ i := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (hc j) (hB k hk0 hk j i hi x) (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have hcount : (Finset.univ.filter (fun j =>
      c j • iteratedFDeriv ℝ i (highPeriodicTensor d k j) x ≠ 0)).card ≤ 2 ^ d := by
    apply (Finset.card_le_card (show Finset.univ.filter (fun j =>
        c j • iteratedFDeriv ℝ i (highPeriodicTensor d k j) x ≠ 0) ⊆
        Finset.univ.filter (fun j => iteratedFDeriv ℝ i (highPeriodicTensor d k j) x ≠ 0) from ?_)).trans
      (highPeriodicTensor_derivative_overlap d k hk i x)
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hz
    exact (Finset.mem_filter.mp hj).2 (by rw [hz, smul_zero])
  have hs := finite_sum_norm_le_active_count
    (fun j => c j • iteratedFDeriv ℝ i (highPeriodicTensor d k j) x)
    (2 ^ d) (B * (k : ℝ) ^ i) (mul_nonneg hB0 (pow_nonneg (Nat.cast_nonneg k) _)) hbound hcount
  have hh := mul_le_mul_of_nonneg_left hs (abs_nonneg η)
  push_cast at hh
  convert hh using 1 <;> ring

/-- Combining the uniform derivative bound and the next-derivative
Lipschitz bound preserves the fractional exponent, uniformly in resolution. -/
theorem holder_of_scaled_sup_and_lipschitz (k r A α q : ℝ)
    (hk : 0 < k) (hr : 0 ≤ r) (hA : 0 ≤ A) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsup : q ≤ 2 * A * k ^ (-α))
    (hlip : q ≤ A * k ^ (1 - α) * r) :
    q ≤ 2 * A * r ^ α := by
  by_cases hr0 : r = 0
  · subst r
    simpa only [mul_zero, Real.zero_rpow hα0.ne'] using hlip
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hkr : k * r ≤ 1
  · have hp : (k * r) ^ (1 - α) ≤ 1 :=
      Real.rpow_le_one (mul_nonneg hk.le hr) hkr (sub_nonneg.mpr hα1)
    have hid : k ^ (1 - α) * r = (k * r) ^ (1 - α) * r ^ α := by
      rw [Real.mul_rpow hk.le hr]
      rw [mul_assoc, ← Real.rpow_add hrpos]
      simp only [sub_add_cancel, Real.rpow_one]
    have hsmall : A * k ^ (1 - α) * r ≤ A * r ^ α := by
      calc
        _ = A * ((k * r) ^ (1 - α) * r ^ α) := by rw [← hid]; ring
        _ ≤ A * (1 * r ^ α) := by gcongr
        _ = _ := by ring
    have hpositive : 0 ≤ A * r ^ α := mul_nonneg hA (Real.rpow_nonneg hr _)
    exact (hlip.trans hsmall).trans (by nlinarith)
  · have hp : 1 ≤ (k * r) ^ α := Real.one_le_rpow (le_of_not_ge hkr) hα0.le
    have hkinv : k ^ (-α) ≤ r ^ α := by
      rw [Real.rpow_neg hk.le, ← one_div]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hk α)).mpr
      simpa only [Real.mul_rpow hk.le hr, one_mul, mul_comm] using hp
    exact hsup.trans (mul_le_mul_of_nonneg_left hkinv (by positivity))

theorem multiIndexBasis_norm {d : ℕ} (γ : Fin d → ℕ) (j : Fin (∑ r, γ r)) :
    ‖multiIndexBasis γ j‖ = 1 := by
  simp [multiIndexBasis, wordBasis, Pi.norm_single]

theorem multiPartial_norm_le_iterated {d : ℕ} (F : Covariate d → ℝ)
    (hF : ContDiff ℝ ∞ F) (γ : Fin d → ℕ) (x : Covariate d) :
    |multiPartial F γ x| ≤ ‖iteratedFDeriv ℝ (∑ r, γ r) F x‖ := by
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x)]
  have hh := (iteratedFDeriv ℝ (∑ r, γ r) F x).le_opNorm (multiIndexBasis γ)
  simpa only [Real.norm_eq_abs, multiIndexBasis_norm, Finset.prod_const_one, mul_one] using hh

theorem multiPartial_diff_norm_le_iterated {d : ℕ} (F : Covariate d → ℝ)
    (hF : ContDiff ℝ ∞ F) (γ : Fin d → ℕ) (x y : Covariate d) :
    |multiPartial F γ x - multiPartial F γ y| ≤
      ‖iteratedFDeriv ℝ (∑ r, γ r) F x - iteratedFDeriv ℝ (∑ r, γ r) F y‖ := by
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x),
    multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl y (mem_univ y)]
  have hh := (iteratedFDeriv ℝ (∑ r, γ r) F x -
    iteratedFDeriv ℝ (∑ r, γ r) F y).le_opNorm (multiIndexBasis γ)
  simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs, multiIndexBasis_norm,
    Finset.prod_const_one, mul_one] using hh

theorem covariate_norm_le_euclidean {d : ℕ} (x : Covariate d) : ‖x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro r
  simpa only [Real.norm_eq_abs, euclideanNorm] using abs_coordinate_le_euclideanNorm x r

/-- The actual scaled Fréchet bounds imply the manuscript's sorted mixed
partial bounds and top-order Euclidean Hölder modulus. -/
theorem mixed_bounds_of_scaled_derivatives {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ) (hF : ContDiff ℝ ∞ F) (k A : ℝ)
    (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ A * k ^ ((q : ℝ) - C.smoothness)) :
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
      |multiPartial F (fun r => (γ r).val) x| ≤ A) ∧
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
      |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        (2 * A) * euclideanNorm (x - y) ^ C.alpha) := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  constructor
  · intro γ hγ x
    apply (multiPartial_norm_le_iterated F hF _ x).trans
    apply (hbound _ (by omega) x).trans
    have hcast : ((∑ r, (γ r).val : ℕ) : ℝ) ≤ C.order := by exact_mod_cast hγ
    have hp : k ^ (((∑ r, (γ r).val : ℕ) : ℝ) - C.smoothness) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith [C.order_lt])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hA
  · intro γ hγ x y
    have hsup (z : Covariate d) : ‖iteratedFDeriv ℝ C.order F z‖ ≤ A * k ^ (-C.alpha) := by
      have he : (C.order : ℝ) - C.smoothness = -C.alpha := by unfold ModelConstants.alpha; ring
      simpa only [he] using hbound C.order (by omega) z
    have hnext (z : Covariate d) : ‖fderiv ℝ (iteratedFDeriv ℝ C.order F) z‖ ≤
        A * k ^ (1 - C.alpha) := by
      rw [norm_fderiv_iteratedFDeriv]
      have he : ((C.order + 1 : ℕ) : ℝ) - C.smoothness = 1 - C.alpha := by
        unfold ModelConstants.alpha
        push_cast
        ring
      simpa only [he] using hbound (C.order + 1) le_rfl z
    have hlarge : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤
        2 * A * k ^ (-C.alpha) := by
      exact (norm_sub_le _ _).trans (by nlinarith [hsup x, hsup y])
    have hsmall : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤
        A * k ^ (1 - C.alpha) * ‖x - y‖ := by
      have hfFinite : ContDiff ℝ (C.order + 1) F := hF.of_le (by simp)
      exact Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z (_hz : z ∈ (univ : Set (Covariate d))) =>
          hfFinite.contDiffAt.differentiableAt_iteratedFDeriv
            (by exact_mod_cast Nat.lt_succ_self C.order))
        (fun z _ => hnext z) convex_univ (mem_univ y) (mem_univ x)
    have hh := holder_of_scaled_sup_and_lipschitz k ‖x - y‖ A C.alpha
      ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖
      hkpos (norm_nonneg _) hA C.alpha_pos C.alpha_le_one hlarge hsmall
    have heval := multiPartial_diff_norm_le_iterated F hF (fun r => (γ r).val) x y
    rw [hγ] at heval
    exact (heval.trans hh).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (covariate_norm_le_euclidean (x - y)) C.alpha_pos.le)
      (by positivity))

theorem holderNorm_of_scaled_derivatives {d : ℕ} (C : ModelConstants d)
    (U : Set (Covariate d)) (F : Covariate d → ℝ) (hF : ContDiff ℝ ∞ F)
    (k A : ℝ) (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ A * k ^ ((q : ℝ) - C.smoothness)) :
    holderNorm U F C.order C.alpha ≤
      ENNReal.ofReal ((((C.order + 1 : ℕ) : ℝ) ^ d + 2) * A) := by
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F hF k A hk hA hbound
  have hh := holderNorm_of_global_mixed_bounds U F C.order C.alpha A (2 * A)
    hA (by positivity) hs hm
  convert hh using 1
  congr 1
  ring

/-- For amplitudes c_f h^s the actual periodic window field has a uniform
original-model Hölder bound, independent of resolution and extension domain. -/
theorem highWindowField_holderNorm_bound {d : ℕ} (C : ModelConstants d) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ cf : ℝ, 0 ≤ cf →
      ∀ c : HighWindowLabels d k → ℝ, (∀ j, |c j| ≤ 1) →
      ∀ U : Set (Covariate d),
        holderNorm U (highWindowField d k (cf * (k : ℝ) ^ (-C.smoothness)) c)
          C.order C.alpha ≤ ENNReal.ofReal (K * cf) := by
  obtain ⟨B, hB0, hB⟩ := highWindowField_derivative_bound d (C.order + 1)
  let B' := max B 1
  let K := (((C.order + 1 : ℕ) : ℝ) ^ d + 2) * (2 : ℝ) ^ d * B'
  have hBp : 0 < B' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro k hk0 hk cf hcf c hc U
  letI := hk0
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hkR
  let A := cf * (2 : ℝ) ^ d * B'
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q (highWindowField d k (cf * (k : ℝ) ^ (-C.smoothness)) c) x‖ ≤
        A * (k : ℝ) ^ ((q : ℝ) - C.smoothness) := by
    intro q hq x
    have hb := hB k hk0 hk (cf * (k : ℝ) ^ (-C.smoothness)) c hc q hq x
    have hp : (k : ℝ) ^ (-C.smoothness) * (k : ℝ) ^ q =
        (k : ℝ) ^ ((q : ℝ) - C.smoothness) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hkpos]
      congr 1
      ring
    have hη : 0 ≤ cf * (k : ℝ) ^ (-C.smoothness) := by positivity
    rw [abs_of_nonneg hη] at hb
    calc
      _ ≤ _ := hb
      _ ≤ cf * (k : ℝ) ^ (-C.smoothness) * (2 : ℝ) ^ d * B' * (k : ℝ) ^ q := by
        gcongr
        exact le_max_left _ _
      _ = _ := by dsimp [A]; rw [← hp]; ring
  have hh := holderNorm_of_scaled_derivatives C U _ (highWindowField_contDiff _ _ _ _)
    (k : ℝ) A hkR hA hs
  convert hh using 1
  congr 1
  dsimp [K, A]
  ring

end NearlyMinimax
