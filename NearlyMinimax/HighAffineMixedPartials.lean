module

public import NearlyMinimax.HighIntrinsicFrame
public import NearlyMinimax.HighPeriodizedFrame
public import NearlyMinimax.DyadicTaylor


@[expose] public section

/-! Exact scaling and local equality of the original mixed partials under
scalar affine charts. These retain the intrinsic C^s normalization. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Scalar affine composition has the exact original mixed-partial scaling. -/
theorem multiPartial_scalar_affine {d : ℕ} (F : Covariate d → ℝ)
    (hF : ContDiff ℝ ∞ F) (a : ℝ) (z : Covariate d) (γ : Fin d → ℕ)
    (x : Covariate d) :
    multiPartial (fun y => F (a • y - z)) γ x =
      a ^ (∑ r, γ r) * multiPartial F γ (a • x - z) := by
  let G : Covariate d → ℝ := fun y => F (y-z)
  have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_id.sub contDiff_const)
  have hA : ContDiff ℝ ∞ (fun y => F (a • y-z)) := by
    apply hF.comp
    exact (contDiff_id.const_smul a).sub contDiff_const
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
    (hA.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x),
    multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
      (hF.of_le (by simp)).contDiffOn γ le_rfl (a • x-z) (mem_univ _)]
  have he := congrFun (iteratedFDeriv_comp_const_smul a
    (hG.of_le (by simp) : ContDiff ℝ ((∑ r, γ r) : ℕ) G)) x
  change iteratedFDeriv ℝ (∑ r, γ r) (fun y => G (a • y)) x = _ at he
  change (iteratedFDeriv ℝ (∑ r, γ r) (fun y => G (a • y)) x) (multiIndexBasis γ) = _
  rw [he, ContinuousMultilinearMap.smul_apply]
  simp only [G, iteratedFDeriv_comp_sub, smul_eq_mul]

/-- Equal smooth germs have equal actual sorted mixed partials. -/
theorem multiPartial_eq_of_eventuallyEq {d : ℕ} {F G : Covariate d → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (x : Covariate d)
    (he : F =ᶠ[𝓝 x] G) (γ : Fin d → ℕ) : multiPartial F γ x = multiPartial G γ x := by
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x),
    multiPartial_eq_iteratedFDeriv univ isOpen_univ _ (∑ r, γ r)
      (hG.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x),
    (he.iteratedFDeriv ℝ (∑ r, γ r)).eq_of_nhds]

theorem highPeriodizedChart_multiPartial_local (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (P : MvPolynomial (Fin d) ℝ) (γ : Fin d → ℕ)
    (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      multiPartial (highPeriodizedChart d k j (highFrameProfile P)) γ x =
        (k : ℝ) ^ (∑ r, γ r) * multiPartial (highFrameProfile P) γ
          (fun r => (k : ℝ)*x r-z r) := by
  obtain ⟨z,hz,he⟩ := highPeriodizedChart_eventuallyEq_single d k hk j _
    (highFrameProfile_zero_of_window_zero P) x
  refine ⟨z,hz,?_⟩
  rw [multiPartial_eq_of_eventuallyEq
    (highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff P)
      (highFrameProfile_zero_of_window_zero P))
    (show ContDiff ℝ ∞ (fun y : Covariate d => highFrameProfile P
      (fun r => (k : ℝ)*y r-z r)) from by
      apply (highFrameProfile_contDiff P).comp
      fun_prop) x he γ]
  exact multiPartial_scalar_affine _ (highFrameProfile_contDiff P) (k : ℝ)
    (fun r => (z r : ℝ)) γ x

end NearlyMinimax
