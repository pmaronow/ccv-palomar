module

public import NearlyMinimax.HighIntrinsicPeriodizedBounds
public import NearlyMinimax.HighNearestChart
public import NearlyMinimax.IntrinsicProfileAmplitude


@[expose] public section

/-! The literal intrinsic-ball Hölder transfer through true periodic charts.
Nearest-copy formulas and compact support handle zero and boundary charts. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
namespace NearlyMinimax
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem integer_congruent_separation (k : ℕ) {z q : ℤ}
    (hres : (z : ZMod k) = (q : ZMod k)) (hne : z ≠ q) :
    (k : ℝ) ≤ |(q : ℝ)-z| := by
  obtain ⟨b,hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp hres
  have hb0 : b ≠ 0 := by
    intro hh
    rw [hh,mul_zero] at hb
    exact hne (by omega)
  have habs : (1 : ℤ) ≤ |b| := by
    have h := abs_pos.mpr hb0
    omega
  have hs : (k : ℤ) ≤ |q-z| := by
    rw [hb,abs_mul,abs_of_nonneg (Int.natCast_nonneg k)]
    nlinarith
  exact_mod_cast hs

 theorem highPeriodizedChart_multiPartial_nearest (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (P : MvPolynomial (Fin d) ℝ) (γ : Fin d → ℕ)
    (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      (∀ r, |(k : ℝ)*x r-z r| ≤ (k : ℝ)/2) ∧
      multiPartial (highPeriodizedChart d k j (highFrameProfile P)) γ x =
        (k : ℝ) ^ (∑ r, γ r) * multiPartial (highFrameProfile P) γ
          (fun r => (k : ℝ)*x r-z r) := by
  obtain ⟨z,hz,hclose,he⟩ := highPeriodizedChart_nearest_eventuallyEq_single d k hk j _
    (highFrameProfile_zero_of_window_zero P) x
  refine ⟨z,hz,hclose,?_⟩
  rw [multiPartial_eq_of_eventuallyEq
    (highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff P)
      (highFrameProfile_zero_of_window_zero P))
    (show ContDiff ℝ ∞ (fun y : Covariate d => highFrameProfile P
      (fun r => (k : ℝ)*y r-z r)) from by
      apply (highFrameProfile_contDiff P).comp
      fun_prop) x he γ]
  exact multiPartial_scalar_affine _ (highFrameProfile_contDiff P) (k : ℝ)
    (fun r => (z r : ℝ)) γ x

 theorem highFrameProfile_multiPartial_other_nearest_zero (d k : ℕ) (hk : 4 ≤ k)
    (P : MvPolynomial (Fin d) ℝ) (γ : Fin d → ℕ) (x : Covariate d)
    (z q : Fin d → ℤ) (hres : ∀ r, (z r : ZMod k) = (q r : ZMod k))
    (hclose : ∀ r, |(k : ℝ)*x r-z r| ≤ (k : ℝ)/2) (hne : z ≠ q) :
    multiPartial (highFrameProfile P) γ (fun r => (k : ℝ)*x r-q r) = 0 := by
  by_contra hn
  have hsupport := highFrameProfile_multiPartial_support_bound P γ _ hn
  obtain ⟨r,hr⟩ := not_forall.mp (fun h => hne (funext h))
  have hs := integer_congruent_separation k (hres r) hr
  have ht : |(q r : ℝ)-z r| ≤ |(k : ℝ)*x r-q r|+|(k : ℝ)*x r-z r| := by
    calc
      _ = |((q r : ℝ)-(k : ℝ)*x r)+((k : ℝ)*x r-z r)| := by congr 1; ring
      _ ≤ |(q r : ℝ)-(k : ℝ)*x r|+|(k : ℝ)*x r-z r| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (q r : ℝ) ((k : ℝ)*x r)]
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hc := hclose r
  have hp := hsupport r
  linarith

 theorem euclideanNorm_scalar_affine_difference {d : ℕ} (k : ℝ) (z : Fin d → ℤ)
    (x y : Covariate d) :
    euclideanNorm ((fun r => k*x r-z r)-(fun r => k*y r-z r)) =
      |k| * euclideanNorm (x-y) := by
  have he : ((fun r => k*x r-z r)-(fun r => k*y r-z r)) = k • (x-y) := by
    ext r
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,euclideanNorm_smul]

/-- Each true periodized top partial retains Hölder coefficient one after
spatial scaling, including changes between congruent compact copies. -/
 theorem highPeriodizedChart_intrinsic_top_modulus {d : ℕ} (C : ModelConstants d)
    (k : ℕ) [NeZero k] (hk : 4 ≤ k) (j : HighWindowLabels d k)
    (P : MvPolynomial (Fin d) ℝ)
    (hP : frameCoefficientL1 P ≤ (highIntrinsicFrameConstant C)⁻¹)
    (γ : Fin d → Fin (C.order+1)) (hγ : (∑ r, (γ r).val) = C.order)
    (x y : Covariate d) :
    |multiPartial (highPeriodizedChart d k j (highFrameProfile P)) (fun r => (γ r).val) x -
      multiPartial (highPeriodizedChart d k j (highFrameProfile P)) (fun r => (γ r).val) y| ≤
      (k : ℝ)^C.order * ((k : ℝ)*euclideanNorm (x-y))^C.alpha := by
  obtain ⟨z,hz,hzx,hex⟩ := highPeriodizedChart_multiPartial_nearest d k hk j P
    (fun r => (γ r).val) x
  obtain ⟨q,hq,hqy,hey⟩ := highPeriodizedChart_multiPartial_nearest d k hk j P
    (fun r => (γ r).val) y
  rw [hex,hey,hγ,← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg k) _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg k) C.order)
  have hmod (a : Fin d → ℤ) := highFrameProfile_intrinsic_ball_modulus C P hP γ hγ
    (fun r => (k : ℝ)*x r-a r) (fun r => (k : ℝ)*y r-a r)
  simp only [euclideanNorm_scalar_affine_difference,abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)] at hmod
  by_cases he : z = q
  · subst q
    exact hmod z
  have hzxq := highFrameProfile_multiPartial_other_nearest_zero d k hk P
    (fun r => (γ r).val) x z q (fun r => (hz r).trans (hq r).symm) hzx he
  have hqyz := highFrameProfile_multiPartial_other_nearest_zero d k hk P
    (fun r => (γ r).val) y q z (fun r => (hq r).trans (hz r).symm) hqy (Ne.symm he)
  by_cases hx : multiPartial (highFrameProfile P) (fun r => (γ r).val)
      (fun r => (k : ℝ)*x r-z r) = 0
  · rw [hx]
    have h := hmod q
    rw [hzxq] at h
    exact h
  by_cases hy : multiPartial (highFrameProfile P) (fun r => (γ r).val)
      (fun r => (k : ℝ)*y r-q r) = 0
  · rw [hy]
    have h := hmod z
    rw [hqyz] at h
    exact h
  have hsx := highFrameProfile_multiPartial_support_bound P (fun r => (γ r).val) _ hx
  have hsy := highFrameProfile_multiPartial_support_bound P (fun r => (γ r).val) _ hy
  obtain ⟨r,hr⟩ := not_forall.mp (fun h => he (funext h))
  have hs := integer_congruent_separation k ((hz r).trans (hq r).symm) hr
  have ht : |(q r : ℝ)-z r| ≤ |(k : ℝ)*y r-q r|+
      |(k : ℝ)*(x r-y r)|+|(k : ℝ)*x r-z r| := by
    calc
      _ = |((q r : ℝ)-(k : ℝ)*y r)+((k : ℝ)*y r-(k : ℝ)*x r)+
          ((k : ℝ)*x r-z r)| := by congr 1; ring
      _ ≤ |((q r : ℝ)-(k : ℝ)*y r)+((k : ℝ)*y r-(k : ℝ)*x r)|+
          |(k : ℝ)*x r-z r| := abs_add_le _ _
      _ ≤ (|(q r : ℝ)-(k : ℝ)*y r|+|(k : ℝ)*y r-(k : ℝ)*x r|)+
          |(k : ℝ)*x r-z r| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (q r : ℝ) ((k : ℝ)*y r)]
                  congr 2
                  rw [← mul_sub,abs_mul,abs_mul,abs_sub_comm]
  have hc : |(k : ℝ)*(x r-y r)| ≤ (k : ℝ)*euclideanNorm (x-y) := by
    rw [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left
      (abs_coordinate_le_euclideanNorm (x-y) r) (Nat.cast_nonneg k)
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 1 ≤ (k : ℝ)*euclideanNorm (x-y) := by
    have hx' := hsx r
    have hy' := hsy r
    linarith
  have hp := Real.one_le_rpow h1 C.alpha_pos.le
  have ha := highFrameProfile_intrinsic_top_amplitude C P hP γ hγ
    (fun r => (k : ℝ)*x r-z r)
  have hb := highFrameProfile_intrinsic_top_amplitude C P hP γ hγ
    (fun r => (k : ℝ)*y r-q r)
  have hab : |multiPartial (highFrameProfile P) (fun r => (γ r).val)
      (fun r => (k : ℝ)*x r-z r) -
      multiPartial (highFrameProfile P) (fun r => (γ r).val)
      (fun r => (k : ℝ)*y r-q r)| ≤ 1 := by
    have h := abs_add_le
      (multiPartial (highFrameProfile P) (fun r => (γ r).val) (fun r => (k : ℝ)*x r-z r))
      (-multiPartial (highFrameProfile P) (fun r => (γ r).val) (fun r => (k : ℝ)*y r-q r))
    rw [abs_neg,← sub_eq_add_neg] at h
    linarith
  exact hab.trans hp

end NearlyMinimax
