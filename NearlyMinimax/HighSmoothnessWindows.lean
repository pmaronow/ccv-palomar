module

public import NearlyMinimax.Model


@[expose] public section

/-! Smooth compact normalized lattice windows for the high-smoothness prior.
The denominator is an actual locally finite sum of integer translates. -/

noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

def highWindowBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 3 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def highWindowSeed : ℝ → ℝ := highWindowBump

theorem highWindowSeed_contDiff : ContDiff ℝ ∞ highWindowSeed :=
  highWindowBump.contDiff

theorem highWindowSeed_nonneg (x : ℝ) : 0 ≤ highWindowSeed x :=
  highWindowBump.nonneg

theorem highWindowSeed_le_one (x : ℝ) : highWindowSeed x ≤ 1 :=
  highWindowBump.le_one

theorem highWindowSeed_eq_one (x : ℝ) (hx : |x| ≤ 1 / 2) : highWindowSeed x = 1 := by
  apply highWindowBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, highWindowBump] using hx

theorem highWindowSeed_eq_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) : highWindowSeed x = 0 := by
  apply highWindowBump.zero_of_le_dist
  simpa [Real.dist_eq, highWindowBump] using hx

/-- Any family of unit-radius integer translates is locally finite. -/
theorem integerTranslate_locallyFinite (g : ℝ → ℝ)
    (hg : ∀ x, 1 ≤ |x| → g x = 0) :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => g (x - j))) := by
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (finite_Icc (⌊x⌋ - 3) (⌊x⌋ + 3)).subset
  intro j hj
  obtain ⟨y, hy, hnear⟩ := hj
  have hdist : |y - j| < 1 := by
    by_contra h
    exact hy (hg _ (not_lt.mp h))
  have hd := abs_lt.mp hdist
  have hfloor := Int.floor_le x
  have hceil := Int.lt_floor_add_one x
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith [hnear.1, hnear.2]
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith [hnear.1, hnear.2]

def highWindowEnergy (x : ℝ) : ℝ := ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2

theorem highWindowEnergy_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => highWindowSeed (x - j) ^ 2)) := by
  apply integerTranslate_locallyFinite (fun x => highWindowSeed x ^ 2)
  intro x hx
  rw [highWindowSeed_eq_zero x (by linarith)]
  norm_num

theorem highWindowEnergy_contDiff : ContDiff ℝ ∞ highWindowEnergy := by
  unfold highWindowEnergy
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ highWindowEnergy_locallyFinite
  intro j
  apply ContDiff.contMDiff
  exact (highWindowSeed_contDiff.comp (contDiff_id.sub contDiff_const)).pow 2

theorem highWindowEnergy_lower (x : ℝ) : 1 ≤ highWindowEnergy x := by
  let j : ℤ := ⌊x + 1 / 2⌋
  have hj0 := Int.floor_le (x + 1 / 2)
  have hj1 := Int.lt_floor_add_one (x + 1 / 2)
  have hclose : |x - j| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [j]; linarith,
    by dsimp [j]; linarith⟩
  have hone := highWindowSeed_eq_one (x - j) hclose
  have hle := single_le_finsum j (highWindowEnergy_locallyFinite.point_finite x)
    (fun z : ℤ => sq_nonneg (highWindowSeed (x - z)))
  simpa [highWindowEnergy, hone] using hle

theorem highWindowEnergy_pos (x : ℝ) : 0 < highWindowEnergy x :=
  lt_of_lt_of_le (by norm_num) (highWindowEnergy_lower x)

theorem highWindowEnergy_integer_periodic (x : ℝ) (k : ℤ) :
    highWindowEnergy (x + k) = highWindowEnergy x := by
  unfold highWindowEnergy
  calc
    (∑ᶠ j : ℤ, highWindowSeed (x + k - j) ^ 2) =
      ∑ᶠ j : ℤ, highWindowSeed (x - (j - k : ℤ)) ^ 2 := by
        apply finsum_congr
        intro j
        congr 2
        push_cast
        ring
    _ = _ := finsum_comp (g := fun j : ℤ => highWindowSeed (x - j) ^ 2)
      (fun j : ℤ => j - k) (by
      constructor
      · intro i j h
        change i - k = j - k at h
        simpa only [sub_left_inj] using h
      · intro j
        exact ⟨j + k, by dsimp; ring⟩)

def highWindowProfile (x : ℝ) : ℝ := highWindowSeed x / Real.sqrt (highWindowEnergy x)

theorem highWindowProfile_contDiff : ContDiff ℝ ∞ highWindowProfile := by
  exact highWindowSeed_contDiff.div
    (highWindowEnergy_contDiff.sqrt (fun x => (highWindowEnergy_pos x).ne'))
    (fun x => (Real.sqrt_pos.mpr (highWindowEnergy_pos x)).ne')

theorem highWindowProfile_nonneg (x : ℝ) : 0 ≤ highWindowProfile x :=
  div_nonneg (highWindowSeed_nonneg x) (Real.sqrt_nonneg _)

theorem highWindowProfile_le_one (x : ℝ) : highWindowProfile x ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (highWindowEnergy x) := by
    simpa using Real.sqrt_le_sqrt (highWindowEnergy_lower x)
  exact (div_le_one (Real.sqrt_pos.mpr (highWindowEnergy_pos x))).mpr
    ((highWindowSeed_le_one x).trans hs)

theorem highWindowProfile_eq_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) :
    highWindowProfile x = 0 := by
  simp [highWindowProfile, highWindowSeed_eq_zero x hx]

theorem highWindowProfile_hasCompactSupport : HasCompactSupport highWindowProfile := by
  apply highWindowBump.hasCompactSupport.mono'
  intro x hx
  apply subset_tsupport highWindowSeed
  change highWindowSeed x ≠ 0
  intro hseed
  exact hx (by simp [highWindowProfile, hseed])

theorem highWindowProfile_sq_partition (x : ℝ) :
    (∑ᶠ j : ℤ, highWindowProfile (x - j) ^ 2) = 1 := by
  have hE := (highWindowEnergy_pos x).ne'
  calc
    (∑ᶠ j : ℤ, highWindowProfile (x - j) ^ 2) =
      ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2 * (highWindowEnergy x)⁻¹ := by
        apply finsum_congr
        intro j
        have hp : highWindowEnergy (x - j) = highWindowEnergy x := by
          simpa [sub_eq_add_neg] using highWindowEnergy_integer_periodic x (-j)
        rw [highWindowProfile, div_pow, hp, Real.sq_sqrt (highWindowEnergy_pos x).le]
        rfl
    _ = highWindowEnergy x * (highWindowEnergy x)⁻¹ :=
      (finsum_mul (fun j : ℤ => highWindowSeed (x - j) ^ 2) _).symm
    _ = 1 := mul_inv_cancel₀ hE

/-- Every fixed derivative order has a finite uniform profile bound. -/
theorem highWindowProfile_derivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ m, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i highWindowProfile x‖ ≤ C :=
  highWindowProfile_hasCompactSupport.exists_bound_iteratedFDeriv
    highWindowProfile_contDiff m

theorem highWindowProfile_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => highWindowProfile (x - j))) := by
  apply integerTranslate_locallyFinite highWindowProfile
  intro x hx
  exact highWindowProfile_eq_zero x (by linarith)

/-- Tensor profile supported strictly inside the manuscript's chart Q. -/
def highWindowTensor (d : ℕ) (x : Covariate d) : ℝ :=
  ∏ i, highWindowProfile (x i)

theorem highWindowTensor_contDiff (d : ℕ) : ContDiff ℝ ∞ (highWindowTensor d) := by
  apply contDiff_prod
  intro i hi
  exact highWindowProfile_contDiff.comp (contDiff_apply ℝ ℝ i)

theorem highWindowTensor_nonneg (d : ℕ) (x : Covariate d) : 0 ≤ highWindowTensor d x :=
  Finset.prod_nonneg (fun i _ => highWindowProfile_nonneg (x i))

theorem highWindowTensor_le_one (d : ℕ) (x : Covariate d) : highWindowTensor d x ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i hi
    exact highWindowProfile_nonneg _
  · intro i hi
    exact highWindowProfile_le_one _

theorem highWindowTensor_support_bound {d : ℕ} {x : Covariate d}
    (hx : highWindowTensor d x ≠ 0) : ∀ i, |x i| < 3 / 4 := by
  intro i
  by_contra hi
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (highWindowProfile_eq_zero _ (not_lt.mp hi))

theorem highWindowTensor_hasCompactSupport (d : ℕ) : HasCompactSupport (highWindowTensor d) := by
  apply (isCompact_closedBall (0 : Covariate d) (3 / 4 : ℝ)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hx i).le

theorem highWindowTensor_sq_partition (d : ℕ) (x : Covariate d) :
    (∑ᶠ j : Fin d → ℤ, highWindowTensor d (fun i => x i - j i) ^ 2) = 1 := by
  let S : Fin d → Finset ℤ := fun i =>
    (highWindowProfile_locallyFinite.point_finite (x i)).toFinset
  have hs : support (fun j : Fin d → ℤ =>
      highWindowTensor d (fun i => x i - j i) ^ 2) ⊆ ↑(Fintype.piFinset S) := by
    intro j hj
    apply Fintype.mem_piFinset.mpr
    intro i
    change j i ∈ (highWindowProfile_locallyFinite.point_finite (x i)).toFinset
    apply (highWindowProfile_locallyFinite.point_finite (x i)).mem_toFinset.mpr
    change highWindowProfile (x i - j i) ≠ 0
    intro hzero
    apply hj
    simp only [highWindowTensor]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
    norm_num
  rw [finsum_eq_finsetSum_of_support_subset _ hs]
  simp only [highWindowTensor, ← Finset.prod_pow]
  rw [← Finset.prod_univ_sum S (fun i j => highWindowProfile (x i - j) ^ 2)]
  have hsum (i : Fin d) :
      (∑ j ∈ S i, highWindowProfile (x i - j) ^ 2) = 1 := by
    rw [← highWindowProfile_sq_partition (x i)]
    symm
    apply finsum_eq_finsetSum_of_support_subset
    intro j hj
    change j ∈ (highWindowProfile_locallyFinite.point_finite (x i)).toFinset
    apply (highWindowProfile_locallyFinite.point_finite (x i)).mem_toFinset.mpr
    change highWindowProfile (x i - j) ≠ 0
    intro hz
    exact hj (by simp [hz])
  simp only [hsum, Finset.prod_const_one]

theorem highWindowTensor_derivative_bound (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ m, ∀ x : Covariate d,
      ‖iteratedFDeriv ℝ i (highWindowTensor d) x‖ ≤ C :=
  (highWindowTensor_hasCompactSupport d).exists_bound_iteratedFDeriv
    (highWindowTensor_contDiff d) m

/-- A finite-period window is the actual sum over its integer residue class. -/
def highPeriodicWindow (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0

theorem highPeriodicWindow_locallyFinite (k : ℕ) (j : ZMod k) :
    LocallyFinite (fun z : ℤ => support (fun x : ℝ =>
      if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0)) := by
  apply (highWindowProfile_locallyFinite.preimage_continuous
    (continuous_const.mul continuous_id)).subset
  intro z x hx
  by_cases hz : (z : ZMod k) = j
  · simpa [hz] using hx
  · simp [hz] at hx

theorem highPeriodicWindow_contDiff (k : ℕ) (j : ZMod k) :
    ContDiff ℝ ∞ (highPeriodicWindow k j) := by
  unfold highPeriodicWindow
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodicWindow_locallyFinite k j)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : (z : ZMod k) = j
  · simp only [if_pos hz]
    exact highWindowProfile_contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · simp only [if_neg hz]
    exact contDiff_const

theorem highPeriodicWindow_nonneg (k : ℕ) (j : ZMod k) (x : ℝ) :
    0 ≤ highPeriodicWindow k j x := by
  apply finsum_nonneg
  intro z
  split_ifs
  · exact highWindowProfile_nonneg _
  · exact le_rfl

theorem highPeriodicWindow_support_subsingleton (k : ℕ) (hk : 2 ≤ k)
    (j : ZMod k) (x : ℝ) :
    (support (fun z : ℤ => if (z : ZMod k) = j then
      highWindowProfile ((k : ℝ) * x - z) else 0)).Subsingleton := by
  intro z hz q hq
  have hzj : (z : ZMod k) = j := by
    by_contra h
    exact hz (by simp [h])
  have hqj : (q : ZMod k) = j := by
    by_contra h
    exact hq (by simp [h])
  have hzd : |(k : ℝ) * x - z| < 3 / 4 := by
    by_contra h
    exact hz (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])
  have hqd : |(k : ℝ) * x - q| < 3 / 4 := by
    by_contra h
    exact hq (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])
  have hdiv : (k : ℤ) ∣ q - z := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp
    (hzj.trans hqj.symm)
  obtain ⟨l, hl⟩ := hdiv
  have hdiff : |(q : ℝ) - z| < 3 / 2 := by
    have h1 := abs_lt.mp hzd
    have h2 := abs_lt.mp hqd
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdiffZ : |q - z| < (2 : ℤ) := by
    apply (Int.cast_lt (R := ℝ)).mp
    push_cast
    linarith
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hl0 : l = 0 := by
    by_contra h
    have habsl : (1 : ℤ) ≤ |l| := by
      have hpos := abs_pos.mpr h
      omega
    have hm : (2 : ℤ) ≤ |(k : ℤ) * l| := by
      rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ k)]
      nlinarith
    rw [← hl] at hm
    omega
  simp only [hl0, mul_zero] at hl
  omega

theorem finsum_sq_of_subsingleton_support (f : ℤ → ℝ) (hs : (support f).Subsingleton) :
    (∑ᶠ z, f z) ^ 2 = ∑ᶠ z, f z ^ 2 := by
  by_cases hn : ∃ z, f z ≠ 0
  · obtain ⟨z, hz⟩ := hn
    have hzero : ∀ q, q ≠ z → f q = 0 := by
      intro q hq
      by_contra h
      exact hq (hs h hz)
    rw [finsum_eq_single f z hzero, finsum_eq_single (fun q => f q ^ 2) z
      (fun q hq => by rw [hzero q hq]; norm_num)]
  · have hzero : ∀ z, f z = 0 := by simpa using hn
    simp only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), finsum_zero]

theorem highPeriodicWindow_sq_partition (k : ℕ) [NeZero k] (hk : 2 ≤ k) (x : ℝ) :
    (∑ j : ZMod k, highPeriodicWindow k j x ^ 2) = 1 := by
  have hs (j : ZMod k) : highPeriodicWindow k j x ^ 2 =
      ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) ^ 2 else 0 := by
    rw [highPeriodicWindow, finsum_sq_of_subsingleton_support _
      (highPeriodicWindow_support_subsingleton k hk j x)]
    apply finsum_congr
    intro z
    split_ifs <;> simp
  simp only [hs]
  rw [sum_finsum_comm]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact highWindowProfile_sq_partition _
  · intro j hj
    apply (highPeriodicWindow_locallyFinite k j).point_finite x |>.subset
    intro z hz
    change (if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0) ≠ 0
    change (if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) ^ 2 else 0) ≠ 0 at hz
    by_cases hzj : (z : ZMod k) = j
    · simp only [ite_eq_left hzj] at hz ⊢
      exact fun h => hz (by rw [h]; norm_num)
    · exact False.elim (hz (by simp [hzj]))

theorem highPeriodicWindow_le_one (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : ZMod k) (x : ℝ) : highPeriodicWindow k j x ≤ 1 := by
  have hsq : highPeriodicWindow k j x ^ 2 ≤ 1 := by
    rw [← highPeriodicWindow_sq_partition k hk x]
    exact Finset.single_le_sum (fun z _ => sq_nonneg (highPeriodicWindow k z x))
      (Finset.mem_univ j)
  nlinarith [highPeriodicWindow_nonneg k j x]

theorem highPeriodicWindow_support_lift (k : ℕ) (j : ZMod k) (x : ℝ)
    (hx : highPeriodicWindow k j x ≠ 0) :
    ∃ z : ℤ, (z : ZMod k) = j ∧ |(k : ℝ) * x - z| < 3 / 4 := by
  have hterm : ∃ z : ℤ, (if (z : ZMod k) = j then
      highWindowProfile ((k : ℝ) * x - z) else 0) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (by simp only [highPeriodicWindow, h, finsum_zero])
  obtain ⟨z, hz⟩ := hterm
  refine ⟨z, ?_, ?_⟩
  · by_contra h
    exact hz (by simp [h])
  · by_contra h
    exact hz (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])

theorem highPeriodicWindow_periodic (k : ℕ) (j : ZMod k) :
    Function.Periodic (highPeriodicWindow k j) 1 := by
  intro x
  unfold highPeriodicWindow
  calc
    (∑ᶠ z : ℤ, if (z : ZMod k) = j then
        highWindowProfile ((k : ℝ) * (x + 1) - z) else 0) =
      ∑ᶠ z : ℤ, if ((z - k : ℤ) : ZMod k) = j then
        highWindowProfile ((k : ℝ) * x - (z - k : ℤ)) else 0 := by
      apply finsum_congr
      intro z
      have hres : ((z - k : ℤ) : ZMod k) = (z : ZMod k) := by simp
      rw [hres]
      congr 2
      push_cast
      ring
    _ = _ := finsum_comp (g := fun z : ℤ => if (z : ZMod k) = j then
        highWindowProfile ((k : ℝ) * x - z) else 0) (fun z : ℤ => z - k) (by
      constructor
      · intro z q h
        change z - (k : ℤ) = q - k at h
        simpa only [sub_left_inj] using h
      · intro z
        exact ⟨z + k, by dsimp; ring⟩)

abbrev HighWindowLabels (d k : ℕ) := Fin d → ZMod k

/-- The actual finite periodic squared partition in d dimensions. -/
def highPeriodicTensor (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : ℝ :=
  ∏ i, highPeriodicWindow k (j i) (x i)

theorem highPeriodicTensor_contDiff (d k : ℕ) (j : HighWindowLabels d k) :
    ContDiff ℝ ∞ (highPeriodicTensor d k j) := by
  apply contDiff_prod
  intro i hi
  exact (highPeriodicWindow_contDiff k (j i)).comp (contDiff_apply ℝ ℝ i)

theorem highPeriodicTensor_nonneg (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) :
    0 ≤ highPeriodicTensor d k j x :=
  Finset.prod_nonneg (fun i _ => highPeriodicWindow_nonneg k (j i) (x i))

theorem highPeriodicTensor_le_one (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d) : highPeriodicTensor d k j x ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i hi
    exact highPeriodicWindow_nonneg _ _ _
  · intro i hi
    exact highPeriodicWindow_le_one _ hk _ _

theorem highPeriodicTensor_sq_partition (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (x : Covariate d) : (∑ j : HighWindowLabels d k, highPeriodicTensor d k j x ^ 2) = 1 := by
  simp only [highPeriodicTensor, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (j : ZMod k) => highPeriodicWindow k j (x i) ^ 2)]
  simp only [highPeriodicWindow_sq_partition k hk, Finset.prod_const_one]

theorem highPeriodicTensor_support_lift (d k : ℕ) (j : HighWindowLabels d k)
    (x : Covariate d) (hx : highPeriodicTensor d k j x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ i, (z i : ZMod k) = j i) ∧
      ∀ i, |(k : ℝ) * x i - z i| < 3 / 4 := by
  have hcoordinate (i : Fin d) : highPeriodicWindow k (j i) (x i) ≠ 0 := by
    intro h
    exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
  choose z hz using fun i => highPeriodicWindow_support_lift k (j i) (x i) (hcoordinate i)
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2⟩

/-- Around every point, a periodized window agrees with one compact chart
profile, including points where the window is zero. -/
theorem highPeriodicWindow_eventuallyEq_single (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) :
    ∃ z : ℤ, (z : ZMod k) = j ∧ highPeriodicWindow k j =ᶠ[𝓝 x]
      (fun y => highWindowProfile ((k : ℝ) * y - z)) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let l : ℤ := ⌊x - (j.val : ℝ) / k + 1 / 2⌋
  let z : ℤ := (j.val : ℤ) + (k : ℤ) * l
  have hzj : (z : ZMod k) = j := by simp [z, ZMod.natCast_zmod_val]
  have hfloor := Int.floor_le (x - (j.val : ℝ) / k + 1 / 2)
  have hceil := Int.lt_floor_add_one (x - (j.val : ℝ) / k + 1 / 2)
  have hdiv : (k : ℝ) * ((j.val : ℝ) / k) = j.val := by field_simp
  have hclose : |(k : ℝ) * x - z| ≤ (k : ℝ) / 2 := by
    dsimp [z]
    push_cast
    apply abs_le.mpr
    dsimp [l]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hfloor hk0.le,
      mul_lt_mul_of_pos_left hceil hk0]
  refine ⟨z, hzj, ?_⟩
  have hradius : 0 < 1 / (4 * (k : ℝ)) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hradius] with y hy
  have hxy : |(k : ℝ) * y - (k : ℝ) * x| < 1 / 4 := by
    have hdist : |y - x| < 1 / (4 * (k : ℝ)) := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hy
    rw [← mul_sub, abs_mul, abs_of_pos hk0]
    have h := mul_lt_mul_of_pos_left hdist hk0
    have hid : (k : ℝ) * (1 / (4 * (k : ℝ))) = 1 / 4 := by field_simp
    simpa only [hid] using h
  rw [highPeriodicWindow, finsum_eq_single _ z]
  · simp only [hzj, ite_true]
  · intro q hq
    by_cases hqj : (q : ZMod k) = j
    · simp only [hqj, ite_true]
      apply highWindowProfile_eq_zero
      by_contra hdist
      have hqclose : |(k : ℝ) * y - q| < 3 / 4 := not_le.mp hdist
      have hdvd : (k : ℤ) ∣ q - z := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp
        (hzj.trans hqj.symm)
      obtain ⟨b, hb⟩ := hdvd
      have hb0 : b ≠ 0 := by
        intro hb0
        simp only [hb0, mul_zero] at hb
        exact hq (by omega)
      have habs : (1 : ℤ) ≤ |b| := by
        have hpos := abs_pos.mpr hb0
        omega
      have hsepZ : (k : ℤ) ≤ |q - z| := by
        rw [hb, abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ k)]
        nlinarith
      have hsep : (k : ℝ) ≤ |(q : ℝ) - z| := by exact_mod_cast hsepZ
      have htri : |(q : ℝ) - z| ≤ |(k : ℝ) * y - q| +
          |(k : ℝ) * y - (k : ℝ) * x| + |(k : ℝ) * x - z| := by
        calc
          _ = |(q - (k : ℝ) * y) + ((k : ℝ) * y - (k : ℝ) * x) +
              ((k : ℝ) * x - z)| := by congr 1; ring
          _ ≤ |(q - (k : ℝ) * y) + ((k : ℝ) * y - (k : ℝ) * x)| +
              |(k : ℝ) * x - z| := abs_add_le _ _
          _ ≤ |q - (k : ℝ) * y| + |(k : ℝ) * y - (k : ℝ) * x| +
              |(k : ℝ) * x - z| := by
                gcongr
                exact abs_add_le _ _
          _ = _ := by rw [abs_sub_comm (q : ℝ) ((k : ℝ) * y)]
      linarith
    · simp only [hqj, ite_false]

theorem highPeriodicTensor_eventuallyEq_single (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ i, (z i : ZMod k) = j i) ∧
      highPeriodicTensor d k j =ᶠ[𝓝 x]
        (fun y => highWindowTensor d (fun i => (k : ℝ) * y i - z i)) := by
  choose z hz he using fun i => highPeriodicWindow_eventuallyEq_single k hk (j i) (x i)
  refine ⟨z, hz, ?_⟩
  have hcoord (i : Fin d) : ∀ᶠ y : Covariate d in 𝓝 x,
      highPeriodicWindow k (j i) (y i) = highWindowProfile ((k : ℝ) * y i - z i) :=
    (continuous_apply i).continuousAt.eventually (he i)
  filter_upwards [Filter.eventually_all.mpr hcoord] with y hy
  exact Finset.prod_congr rfl (fun i _ => hy i)

theorem smooth_affine_iteratedFDeriv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℝ) (z x : E)
    (n : ℕ) (B : ℝ) (hB : ∀ y, ‖iteratedFDeriv ℝ n F y‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => F (k • y - z)) x‖ ≤ B * |k| ^ n := by
  let g : E →L[ℝ] E := k • ContinuousLinearMap.id ℝ E
  let G : E → ℝ := fun y => F (y - z)
  have hG : ContDiff ℝ n G := (hF.of_le (by simp)).comp
    (contDiff_id.sub contDiff_const)
  have hid := g.iteratedFDerivWithin_comp_right hG.contDiffOn uniqueDiffOn_univ
    (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set E)))
    (x := x) (mem_univ _) (i := n) le_rfl
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hid
  change ‖iteratedFDeriv ℝ n (G ∘ g) x‖ ≤ _
  rw [hid]
  have hg : ‖g‖ ≤ |k| := by
    dsimp [g]
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg k)).trans_eq
      (mul_one _)
  have hGF : ‖iteratedFDeriv ℝ n G (g x)‖ ≤ B := by
    simpa only [G, iteratedFDeriv_comp_sub] using hB (g x - z)
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul hGF (pow_le_pow_left₀ (norm_nonneg g) hg n)
    (pow_nonneg (norm_nonneg g) _) ((norm_nonneg _).trans hGF)

/-- Fixed-order derivative constants are independent of grid resolution;
the actual finite periodic windows have the required h^{-i} scaling. -/
theorem highPeriodicTensor_derivative_bound (d m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ j : HighWindowLabels d k, ∀ i ≤ m, ∀ x : Covariate d,
        ‖iteratedFDeriv ℝ i (highPeriodicTensor d k j) x‖ ≤ B * (k : ℝ) ^ i := by
  obtain ⟨B, hB0, hB⟩ := highWindowTensor_derivative_bound d m
  refine ⟨B, hB0, ?_⟩
  intro k hk0 hk j i hi x
  letI := hk0
  obtain ⟨z, hz, he⟩ := highPeriodicTensor_eventuallyEq_single d k hk j x
  rw [(he.iteratedFDeriv ℝ i).eq_of_nhds]
  have hh := smooth_affine_iteratedFDeriv_bound (highWindowTensor d)
    (highWindowTensor_contDiff d) (k : ℝ) (fun r => (z r : ℝ)) x i B (hB i hi)
  change ‖iteratedFDeriv ℝ i
    (fun y => highWindowTensor d (fun r => (k : ℝ) * y r - z r)) x‖ ≤ B * |(k : ℝ)| ^ i at hh
  rwa [abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)] at hh

theorem highWindowTensor_tsupport_bound {d : ℕ} {x : Covariate d}
    (hx : x ∈ tsupport (highWindowTensor d)) : ∀ i, |x i| ≤ 3 / 4 := by
  have hsub : tsupport (highWindowTensor d) ⊆ Metric.closedBall (0 : Covariate d) (3 / 4 : ℝ) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hy i).le
  have hnorm := hsub hx
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)] at hnorm
  simpa only [Real.norm_eq_abs] using hnorm

/-- The same compact chart support applies to every genuine derivative. -/
theorem highPeriodicTensor_derivative_support_lift (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (i : ℕ) (x : Covariate d)
    (hx : iteratedFDeriv ℝ i (highPeriodicTensor d k j) x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      ∀ r, |(k : ℝ) * x r - z r| ≤ 3 / 4 := by
  obtain ⟨z, hz, he⟩ := highPeriodicTensor_eventuallyEq_single d k hk j x
  let A : Covariate d → ℝ := fun y => highWindowTensor d (fun r => (k : ℝ) * y r - z r)
  have hn : iteratedFDeriv ℝ i
      (fun y => highWindowTensor d (fun r => (k : ℝ) * y r - z r)) x ≠ 0 := by
    rwa [← (he.iteratedFDeriv ℝ i).eq_of_nhds]
  have hsub : support (iteratedFDeriv ℝ i A) ⊆ tsupport A :=
    support_iteratedFDeriv_subset (𝕜 := ℝ) i
  have hs : x ∈ tsupport A := hsub (show x ∈ support (iteratedFDeriv ℝ i A) from hn)
  have hc : Continuous (fun y : Covariate d => fun r => (k : ℝ) * y r - (z r : ℝ)) := by
    fun_prop
  have ht : (fun r => (k : ℝ) * x r - (z r : ℝ)) ∈ tsupport (highWindowTensor d) :=
    (tsupport_comp_subset_preimage (highWindowTensor d) hc) hs
  exact ⟨z, hz, highWindowTensor_tsupport_bound ht⟩

theorem integer_close_three_quarters (t : ℝ) (z : ℤ) (hz : |t - z| ≤ 3 / 4) :
    z = ⌊t⌋ ∨ z = ⌊t⌋ + 1 := by
  have hf := Int.floor_le t
  have hc := Int.lt_floor_add_one t
  have hclose := abs_le.mp hz
  have hlo : ⌊t⌋ ≤ z := by
    by_contra h
    have hcast : (z : ℝ) + 1 ≤ ⌊t⌋ := by exact_mod_cast (by omega : z + 1 ≤ ⌊t⌋)
    linarith
  have hhi : z ≤ ⌊t⌋ + 1 := by
    by_contra h
    have hcast : (⌊t⌋ : ℝ) + 2 ≤ z := by exact_mod_cast (by omega : ⌊t⌋ + 2 ≤ z)
    linarith
  omega

def highActiveLabelBox (d k : ℕ) (x : Covariate d) : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {((⌊(k : ℝ) * x r⌋ : ℤ) : ZMod k),
    ((⌊(k : ℝ) * x r⌋ + 1 : ℤ) : ZMod k)})

theorem highPeriodicTensor_derivative_active_subset (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (i : ℕ) (x : Covariate d) :
    Finset.univ.filter (fun j => iteratedFDeriv ℝ i (highPeriodicTensor d k j) x ≠ 0) ⊆
      highActiveLabelBox d k x := by
  intro j hj
  obtain ⟨z, hz, hclose⟩ := highPeriodicTensor_derivative_support_lift d k hk j i x
    (Finset.mem_filter.mp hj).2
  apply Fintype.mem_piFinset.mpr
  intro r
  have he := integer_close_three_quarters ((k : ℝ) * x r) (z r) (hclose r)
  rcases he with he | he
  · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, true_or]
  · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, or_true]

theorem highActiveLabelBox_card_le (d k : ℕ) (x : Covariate d) :
    (highActiveLabelBox d k x).card ≤ 2 ^ d := by
  unfold highActiveLabelBox
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 2 := by
      apply Finset.prod_le_prod'
      intro r hr
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = 2 ^ d := by simp

/-- The original 2^d pointwise overlap bound also holds for every derivative. -/
theorem highPeriodicTensor_derivative_overlap (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (i : ℕ) (x : Covariate d) :
    (Finset.univ.filter (fun j => iteratedFDeriv ℝ i (highPeriodicTensor d k j) x ≠ 0)).card ≤
      2 ^ d :=
  (Finset.card_le_card (highPeriodicTensor_derivative_active_subset d k hk i x)).trans
    (highActiveLabelBox_card_le d k x)

end NearlyMinimax
