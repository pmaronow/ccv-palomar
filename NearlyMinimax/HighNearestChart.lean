module

public import NearlyMinimax.HighPeriodizedFrame


@[expose] public section

/-! Nearest congruent smooth local representatives for actual periodized
chart profiles, retaining the half-period distance bound even at zeros. -/
noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem highPeriodicWindow_nearest_eventuallyEq_single (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) :
    ∃ z : ℤ, (z : ZMod k) = j ∧ |(k : ℝ) * x - z| ≤ (k : ℝ) / 2 ∧
      highPeriodicWindow k j =ᶠ[𝓝 x]
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
  refine ⟨z, hzj, hclose, ?_⟩
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

theorem highPeriodizedChart_nearest_eventuallyEq_single (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      (∀ r, |(k : ℝ) * x r - z r| ≤ (k : ℝ) / 2) ∧
      highPeriodizedChart d k j G =ᶠ[𝓝 x]
        (fun y => G (fun r => (k : ℝ) * y r - z r)) := by
  choose z hz hc he using fun r => highPeriodicWindow_nearest_eventuallyEq_single k hk (j r) (x r)
  refine ⟨z, hz, hc, ?_⟩
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


end NearlyMinimax
