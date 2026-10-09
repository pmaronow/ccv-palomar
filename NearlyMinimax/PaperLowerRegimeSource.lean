module

public import NearlyMinimax.PaperLowerRegimeHierarchy
public import NearlyMinimax.CompleteSourceRows


@[expose] public section

/-! Genuine complete-source well-definedness and activity, uniformly over
every tuple in the paper's Reg(K). -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem shrunkDensityExponent_eventually_le_plus_one {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∀ᶠ M : ℕ in atTop, shrunkDensityExponent a b M ≤ densityIntervalExponent a b+1 := by
  obtain ⟨Ctau,hCtau,hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  filter_upwards [hcontrol, eventually_ge_atTop (1 : ℕ), eventually_ge_atTop (Nat.ceil Ctau)] with M hτ hm hceil
  have hmR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hCt : Ctau ≤ (M : ℝ) := (Nat.le_ceil Ctau).trans (by exact_mod_cast hceil)
  nlinarith [hτ.2]

theorem paperLowerRegime_uniform_source_guards {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr lam : ℝ) (hK : 1 ≤ K) (hCfr : 1 ≤ Cfr)
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ k : ℕ,
      let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
      let ell := N*Real.exp (-c0*(D : ℝ))
      HighUnionSourceGuards C (M : ℝ) Cfr (completeSourceRows C k D M q Cfr lam ell N mu) ∧
      (∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu) ∧
      (∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hab : C.densityLower < C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  have hc0 : 0 < c0 := by dsimp [c0]; linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_hierarchy hd C Q K c0 1 1 hK hc0.le (by norm_num) (by norm_num)
  let M0 := max M1 (max 2 (Nat.ceil (highCenterResolutionThreshold C)))
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R k
  have hh := hM1 M D ((le_max_left _ _).trans hm) N mu eta R
  have hm2 : 2 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hres : highCenterResolutionThreshold C ≤ (M : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans hm)))
  have hD3 : 3 ≤ D := by
    have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hm2
    have hslope : 2 ≤ paperLowerRegimeDegreeSlope d := by
      unfold paperLowerRegimeDegreeSlope
      linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have hDr : (3 : ℝ) ≤ D := by nlinarith [R.degree_lower]
    exact_mod_cast hDr
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one R.scale
  have hell : 0 < N*Real.exp (-c0*(D : ℝ)) := by positivity
  have hellN : N*Real.exp (-c0*(D : ℝ)) < N := by
    have hD : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have he : Real.exp (-c0*(D : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    simpa only [mul_one] using mul_lt_mul_of_pos_left he hN
  refine ⟨completeSourceRows_guards C k D M q hD3 hq hres Cfr lam _ N mu hCfr hell hellN,?_,?_⟩
  · intro j
    unfold higherBandTargetScale
    exact mul_pos hN (Real.rpow_pos_of_pos (mul_pos R.occupancy_positive R.H_positive) _)
  · intro j hj
    exact (hh.target_count (j.val+3) hj).trans hh.target_resolution

theorem paperLowerRegime_uniform_activity {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr lam : ℝ) (hK : 1 ≤ K) (q : ℕ) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ k : ℕ,
      let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
      let ell := N*Real.exp (-c0*(D : ℝ))
      highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass ≤
        sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam*
          N^2*Real.exp (shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hab : C.densityLower < C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  have hc0 : 1 ≤ c0 := by dsimp [c0]; linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  let Cact := higherBandSourceCact d C.densityLower C.densityUpper c0 lam
  have hCact : 0 ≤ Cact := (higherBandSourceCact_positive d C.densityLower_pos hab).le
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_hierarchy hd C Q K c0 Cact 1 hK (by linarith) hCact (by norm_num)
  have hevent : ∀ᶠ M : ℕ in atTop, M1 ≤ M ∧ 1 ≤ M ∧
      highCenterResolutionThreshold C ≤ (M : ℝ) ∧
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 := by
    filter_upwards [eventually_ge_atTop M1,eventually_ge_atTop (1 : ℕ),
      eventually_ge_atTop (Nat.ceil (highCenterResolutionThreshold C)),
      shrunkDensityExponent_eventually_le_plus_one C.densityLower_pos hab] with M hm hm1 hceil htau
    exact ⟨hm,hm1,(Nat.le_ceil _).trans (by exact_mod_cast hceil),htau⟩
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hevent
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R k
  obtain ⟨hm1,hmpos,hres,htau⟩ := hM0 M hm
  have H := hM1 M D hm1 N mu eta R
  obtain ⟨_,hinterval⟩ := high_source_interval_numeric C (M : ℝ) hres
  have hshrink : C.densityLower+(M : ℝ)⁻¹ < C.densityUpper-(M : ℝ)⁻¹ := by simpa only [one_div] using hinterval
  have hD : 1 ≤ D := by
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hmpos
    have hslope : 2 ≤ paperLowerRegimeDegreeSlope d := by
      unfold paperLowerRegimeDegreeSlope
      linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have hDr : (1 : ℝ) ≤ D := by nlinarith [R.degree_lower]
    exact_mod_cast hDr
  have hDN : (D : ℝ)*Real.exp (c0*(D : ℝ)) ≤ N := by
    have he := Real.exp_le_exp.mpr (show c0*(D : ℝ) ≤ c0*((D : ℝ)+1) by nlinarith)
    exact (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg D)).trans (by simpa only [one_mul] using H.singleton)
  have hb := sourceRows_shrunk_activity_bound (k := k) (M := M) (q := q) hd hD
    C.densityLower C.densityUpper Cfr lam N mu c0
    (higherBandGeometricRatio d D Cact (1+Real.log N) (mu*(1+Real.log N)) 1)
    (higherBandGeometricRatio d D Cact (1+Real.log N) (mu*(1+Real.log N)) 2)
    C.densityLower_pos hshrink htau hc0 R.scale R.occupancy_positive.le H.base hDN
    rfl rfl H.ratio_small H.ratios H.ratio_degree
  have hc : sourceActivityConstant d q Cfr
      (uniformOrdinaryDensityActivityBase C.densityLower C.densityUpper c0) lam ≤
      sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam := by
    unfold sourceSaddleActivityConstant
    dsimp [c0]
    linarith
  have ho := hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg N))
    (Real.exp_pos _).le)
  rw [show (M : ℝ)⁻¹ = 1/(M : ℝ) by simp] at ho
  change highRowTotalMass (sourceRowData d k D M q (C.densityLower+1/(M : ℝ))
    (C.densityUpper-1/(M : ℝ)) Cfr lam (N*Real.exp (-c0*(D : ℝ))) N mu).rowMass ≤ _
  exact ho

end NearlyMinimax
