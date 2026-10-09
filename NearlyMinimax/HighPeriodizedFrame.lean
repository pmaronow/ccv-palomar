module

public import NearlyMinimax.HighFramePolynomial


@[expose] public section

/-! Actual periodization and smooth local charts for polynomial frame fields. -/
noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem integerLatticeTranslate_locallyFinite (d : ℕ) (G : Covariate d → ℝ)
    (hG : ∀ u, G u ≠ 0 → ∀ r, |u r| < 1) :
    LocallyFinite (fun z : Fin d → ℤ => support (fun x : Covariate d =>
      G (fun r => x r - z r))) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  let S : Fin d → Finset ℤ := fun r => Finset.Icc (⌊x r⌋ - 3) (⌊x r⌋ + 3)
  apply (Fintype.piFinset S).finite_toSet.subset
  intro z hz
  obtain ⟨y, hy, hnear⟩ := hz
  apply Fintype.mem_piFinset.mpr
  intro r
  have hclose := abs_lt.mp (hG (fun r => y r - z r) hy r)
  have hnorm : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hnear
  have hcoord : |y r - x r| < 1 := by
    exact (show |y r - x r| ≤ ‖y - x‖ from by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y - x) r).trans_lt hnorm
  have hcoord' := abs_lt.mp hcoord
  have hfloor := Int.floor_le (x r)
  have hceil := Int.lt_floor_add_one (x r)
  apply Finset.mem_Icc.mpr
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith

def highPeriodizedChart (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  ∑ᶠ z : Fin d → ℤ, if (∀ r, (z r : ZMod k) = j r) then
    G (fun r => (k : ℝ) * x r - z r) else 0

theorem highPeriodizedChart_locallyFinite (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    LocallyFinite (fun z : Fin d → ℤ => support (fun x : Covariate d =>
      if (∀ r, (z r : ZMod k) = j r) then G (fun r => (k : ℝ) * x r - z r) else 0)) := by
  have hlf := integerLatticeTranslate_locallyFinite d G (by
    intro u hu r
    have hw : highWindowTensor d u ≠ 0 := fun h => hu (hG0 u h)
    exact (highWindowTensor_support_bound hw r).trans (by norm_num))
  have hc : Continuous (fun x : Covariate d => fun r => (k : ℝ) * x r) := by fun_prop
  apply (hlf.preimage_continuous hc).subset
  intro z x hx
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · change (if (∀ r, (z r : ZMod k) = j r) then
      G (fun r => (k : ℝ) * x r - z r) else 0) ≠ 0 at hx
    rw [ite_eq_left hz] at hx
    change G (fun r => (k : ℝ) * x r - z r) ≠ 0
    exact hx
  · simp [hz] at hx

theorem highPeriodizedChart_contDiff (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (hG : ContDiff ℝ ∞ G)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    ContDiff ℝ ∞ (highPeriodizedChart d k j G) := by
  unfold highPeriodizedChart
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodizedChart_locallyFinite d k j G hG0)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · simp only [ite_eq_left hz]
    apply hG.comp
    fun_prop
  · simp only [ite_eq_right hz]
    exact contDiff_const

theorem highPeriodicWindow_term_le (k : ℕ) (j : ZMod k) (x : ℝ)
    (z : ℤ) (hz : (z : ZMod k) = j) :
    highWindowProfile ((k : ℝ) * x - z) ≤ highPeriodicWindow k j x := by
  have hh := single_le_finsum z (highPeriodicWindow_locallyFinite k j |>.point_finite x)
    (fun q : ℤ => show 0 ≤ (if (q : ZMod k) = j then
      highWindowProfile ((k : ℝ) * x - q) else 0) from by
      split_ifs
      · exact highWindowProfile_nonneg _
      · exact le_rfl)
  simpa only [ite_eq_left hz, highPeriodicWindow] using hh

/-- Any chart supported by the compact profile has one smooth chart formula
in a neighborhood, including points where that formula is zero. -/
theorem highPeriodizedChart_eventuallyEq_single (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      highPeriodizedChart d k j G =ᶠ[𝓝 x]
        (fun y => G (fun r => (k : ℝ) * y r - z r)) := by
  choose z hz he using fun r => highPeriodicWindow_eventuallyEq_single k hk (j r) (x r)
  refine ⟨z, hz, ?_⟩
  have hcoord (r : Fin d) : ∀ᶠ y : Covariate d in 𝓝 x,
      highPeriodicWindow k (j r) (y r) = highWindowProfile ((k : ℝ) * y r - z r) :=
    (continuous_apply r).continuousAt.eventually (he r)
  filter_upwards [Filter.eventually_all.mpr hcoord] with y hy
  rw [highPeriodizedChart, finsum_eq_single _ z]
  · simp only [ite_eq_left hz]
  · intro q hq
    by_cases hqj : ∀ r, (q r : ZMod k) = j r
    · simp only [ite_eq_left hqj]
      by_contra hnonzero
      have hprof : highWindowTensor d (fun r => (k : ℝ) * y r - q r) ≠ 0 :=
        fun h => hnonzero (hG0 _ h)
      have hqeq : q = z := by
        funext r
        have hqr : highWindowProfile ((k : ℝ) * y r - q r) ≠ 0 := by
          intro hh
          exact hprof (Finset.prod_eq_zero (Finset.mem_univ r) hh)
        have hqpositive : 0 < highWindowProfile ((k : ℝ) * y r - q r) :=
          lt_of_le_of_ne (highWindowProfile_nonneg _) (Ne.symm hqr)
        have hzpositive : 0 < highWindowProfile ((k : ℝ) * y r - z r) := by
          have hh := highPeriodicWindow_term_le k (j r) (y r) (q r) (hqj r)
          rw [hy r] at hh
          exact hqpositive.trans_le hh
        have hqs : q r ∈ support (fun a : ℤ => if (a : ZMod k) = j r then
            highWindowProfile ((k : ℝ) * y r - a) else 0) := by
          simpa only [mem_support, ite_eq_left (hqj r)] using hqr
        have hzs : z r ∈ support (fun a : ℤ => if (a : ZMod k) = j r then
            highWindowProfile ((k : ℝ) * y r - a) else 0) := by
          simpa only [mem_support, ite_eq_left (hz r)] using hzpositive.ne'
        exact highPeriodicWindow_support_subsingleton k (by omega) (j r) (y r) hqs hzs
      exact hq hqeq
    · simp only [ite_eq_right hqj]

theorem highPeriodizedChart_derivative_bound (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ) (hG : ContDiff ℝ ∞ G)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0)
    (q : ℕ) (B : ℝ) (hB : ∀ u, ‖iteratedFDeriv ℝ q G u‖ ≤ B) (x : Covariate d) :
    ‖iteratedFDeriv ℝ q (highPeriodizedChart d k j G) x‖ ≤ B * (k : ℝ) ^ q := by
  obtain ⟨z, hz, he⟩ := highPeriodizedChart_eventuallyEq_single d k hk j G hG0 x
  rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
  have hh := smooth_affine_iteratedFDeriv_bound G hG (k : ℝ)
    (fun r => (z r : ℝ)) x q B hB
  change ‖iteratedFDeriv ℝ q (fun y => G (fun r => (k : ℝ) * y r - z r)) x‖ ≤
    B * |(k : ℝ)| ^ q at hh
  rwa [abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)] at hh

theorem highPeriodizedChart_tsupport_profile (d : ℕ) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    tsupport G ⊆ tsupport (highWindowTensor d) := by
  apply closure_mono
  intro u hu
  exact fun h => hu (hG0 u h)

theorem highPeriodizedChart_derivative_support_lift (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (q : ℕ) (x : Covariate d)
    (hx : iteratedFDeriv ℝ q (highPeriodizedChart d k j G) x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      ∀ r, |(k : ℝ) * x r - z r| ≤ 3 / 4 := by
  obtain ⟨z, hz, he⟩ := highPeriodizedChart_eventuallyEq_single d k hk j G hG0 x
  let A : Covariate d → ℝ := fun y => G (fun r => (k : ℝ) * y r - z r)
  have hn : iteratedFDeriv ℝ q A x ≠ 0 := by
    rwa [← (he.iteratedFDeriv ℝ q).eq_of_nhds]
  have hsub : support (iteratedFDeriv ℝ q A) ⊆ tsupport A :=
    support_iteratedFDeriv_subset (𝕜 := ℝ) q
  have hs : x ∈ tsupport A := hsub (show x ∈ support (iteratedFDeriv ℝ q A) from hn)
  have hc : Continuous (fun y : Covariate d => fun r => (k : ℝ) * y r - (z r : ℝ)) := by
    fun_prop
  have ht : (fun r => (k : ℝ) * x r - (z r : ℝ)) ∈ tsupport G :=
    (tsupport_comp_subset_preimage G hc) hs
  exact ⟨z, hz, highWindowTensor_tsupport_bound
    (highPeriodizedChart_tsupport_profile d G hG0 ht)⟩

theorem highPeriodizedChart_derivative_active_subset (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (G : HighWindowLabels d k → Covariate d → ℝ)
    (hG0 : ∀ j u, highWindowTensor d u = 0 → G j u = 0) (q : ℕ) (x : Covariate d) :
    Finset.univ.filter (fun j => iteratedFDeriv ℝ q (highPeriodizedChart d k j (G j)) x ≠ 0) ⊆
      highActiveLabelBox d k x := by
  intro j hj
  obtain ⟨z, hz, hclose⟩ := highPeriodizedChart_derivative_support_lift d k hk j (G j)
    (hG0 j) q x (Finset.mem_filter.mp hj).2
  apply Fintype.mem_piFinset.mpr
  intro r
  have he := integer_close_three_quarters ((k : ℝ) * x r) (z r) (hclose r)
  rcases he with he | he
  · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, true_or]
  · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, or_true]

theorem highPeriodizedChart_derivative_overlap (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (G : HighWindowLabels d k → Covariate d → ℝ)
    (hG0 : ∀ j u, highWindowTensor d u = 0 → G j u = 0) (q : ℕ) (x : Covariate d) :
    (Finset.univ.filter (fun j => iteratedFDeriv ℝ q (highPeriodizedChart d k j (G j)) x ≠ 0)).card ≤
      2 ^ d :=
  (Finset.card_le_card (highPeriodizedChart_derivative_active_subset d k hk G hG0 q x)).trans
    (highActiveLabelBox_card_le d k x)

def highFrameField (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) (x : Covariate d) : ℝ :=
  η * ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) x

theorem highFrameProfile_zero_of_window_zero {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (u : Covariate d) (hu : highWindowTensor d u = 0) : highFrameProfile P u = 0 := by
  simp only [highFrameProfile, hu, zero_mul]

theorem highFrameField_contDiff (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ ∞ (highFrameField d k η P) := by
  unfold highFrameField
  change ContDiff ℝ ∞ (fun x => η • ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) x)
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro j hj
  exact highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
    (highFrameProfile_zero_of_window_zero (P j))

/-- The coefficient ball is independent of the polynomial degree.  Its
normalization makes every derivative through the fixed order at most one
before the spatial rescaling. -/
theorem highFrameField_derivative_bound (d m : ℕ) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ η : ℝ,
      ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) → ∀ q ≤ m, ∀ x : Covariate d,
      ‖iteratedFDeriv ℝ q (highFrameField d k η P) x‖ ≤
        |η| * (2 : ℝ) ^ d * (k : ℝ) ^ q := by
  obtain ⟨B, hB0, hB⟩ := highFrameProfile_derivative_bound d m
  let Cfr := max B 1
  have hCfr1 : 1 ≤ Cfr := le_max_right _ _
  have hCfr0 : 0 < Cfr := lt_of_lt_of_le (by norm_num) hCfr1
  refine ⟨Cfr, hCfr1, ?_⟩
  intro k hk0 hk η P hP q hq x
  letI := hk0
  have hprofile (j : HighWindowLabels d k) (u : Covariate d) :
      ‖iteratedFDeriv ℝ q (highFrameProfile (P j)) u‖ ≤ 1 := by
    calc
      _ ≤ B * frameCoefficientL1 (P j) := hB (P j) q hq u
      _ ≤ Cfr * Cfr⁻¹ := mul_le_mul (le_max_left _ _) (hP j)
        (frameCoefficientL1_nonneg _) hCfr0.le
      _ = 1 := mul_inv_cancel₀ hCfr0.ne'
  have hchart (j : HighWindowLabels d k) :
      ‖iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x‖ ≤
        (k : ℝ) ^ q := by
    simpa only [one_mul] using highPeriodizedChart_derivative_bound d k hk j _
      (highFrameProfile_contDiff (P j)) (highFrameProfile_zero_of_window_zero (P j))
      q 1 (hprofile j) x
  have hsmooth (j : HighWindowLabels d k) :
      ContDiffAt ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x :=
    ((highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
      (highFrameProfile_zero_of_window_zero (P j))).of_le (by simp)).contDiffAt
  have he : iteratedFDeriv ℝ q (highFrameField d k η P) x =
      η • ∑ j, iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x := by
    change iteratedFDeriv ℝ q
      (fun y => η • ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) y) x = _
    rw [iteratedFDeriv_const_smul_apply' (by
      apply ContDiffAt.sum
      intro j hj
      exact hsmooth j)]
    rw [iteratedFDeriv_fun_sum_apply (fun j _ => hsmooth j)]
  rw [he, norm_smul, Real.norm_eq_abs]
  have hh := finite_sum_norm_le_active_count
    (fun j => iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x)
    (2 ^ d) ((k : ℝ) ^ q) (pow_nonneg (Nat.cast_nonneg k) _) hchart
    (highPeriodizedChart_derivative_overlap d k hk (fun j => highFrameProfile (P j))
      (fun j => highFrameProfile_zero_of_window_zero (P j)) q x)
  have hh' := mul_le_mul_of_nonneg_left hh (abs_nonneg η)
  push_cast at hh'
  convert hh' using 1 <;> ring

/-- Original mixed partials, Euclidean Hölder modulus, and the full original
norm of the actual frame field, uniformly in degree and resolution. -/
theorem highFrameField_model_bounds {d : ℕ} (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ) ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * ((2 : ℝ) ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (((((C.order + 1 : ℕ) : ℝ) ^ d + 2) * (2 : ℝ) ^ d) * cf)) := by
  obtain ⟨Cfr, hCfr1, hCfr⟩ := highFrameField_derivative_bound d (C.order + 1)
  refine ⟨Cfr, hCfr1, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hkR
  have hA : 0 ≤ (2 : ℝ) ^ d * cf := by positivity
  have hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ ((2 : ℝ) ^ d * cf) *
        (k : ℝ) ^ ((q : ℝ) - C.smoothness) := by
    intro q hq x
    have hh := hCfr k hk0 hk (cf * (k : ℝ) ^ (-C.smoothness)) P hP q hq x
    have hη : 0 ≤ cf * (k : ℝ) ^ (-C.smoothness) := by positivity
    rw [abs_of_nonneg hη] at hh
    have hp : (k : ℝ) ^ (-C.smoothness) * (k : ℝ) ^ q =
        (k : ℝ) ^ ((q : ℝ) - C.smoothness) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hkpos]
      congr 1
      ring
    convert hh using 1
    rw [← hp]
    ring
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F
    (highFrameField_contDiff _ _ _ _) (k : ℝ) ((2 : ℝ) ^ d * cf) hkR hA hbound
  have hvalue (x : Covariate d) :
      |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness)) := by
    have hh := hCfr k hk0 hk (cf * (k : ℝ) ^ (-C.smoothness)) P hP 0 (by omega) x
    have hη : 0 ≤ cf * (k : ℝ) ^ (-C.smoothness) := by positivity
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg hη, pow_zero,
      mul_one] at hh
    simpa only [F, mul_comm] using hh
  refine ⟨hvalue, hs, hm, ?_⟩
  intro U
  have hh := holderNorm_of_scaled_derivatives C U F (highFrameField_contDiff _ _ _ _)
    (k : ℝ) ((2 : ℝ) ^ d * cf) hkR hA hbound
  convert hh using 1
  congr 1
  ring

end NearlyMinimax
