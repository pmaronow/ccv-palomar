module

public import NearlyMinimax.FinePairNuisanceFactorialEnergy
public import NearlyMinimax.PaperLowerRegimeAliasNorm
public import NearlyMinimax.PaperLowerRegimeFieldScale


@[expose] public section

/-! The separate literal pair-alias and higher-field nuisance norms satisfy
the two inequalities of (new-pair-alias)/(new-pair-field) for every Reg(K). -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def paperRegimePairAliasConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr Cs : ℝ) (q : ℕ) : ℝ :=
  finePairSaddleAliasFactorialConstant d q C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (densityIntervalExponent C.densityLower C.densityUpper+1)
    (paperLowerRegimeDegreeSlope d+1) (3*Cs)

def paperRegimePairFieldConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr Cs : ℝ) (q : ℕ) : ℝ :=
  1+finePairFieldFactorialConstant d q C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (densityIntervalExponent C.densityLower C.densityUpper+1) (3*Cs)

theorem finePairFieldFactorialConstant_nonneg (d q : ℕ) (ad bd Cfr a rho c0 Cs : ℝ) :
    0 ≤ finePairFieldFactorialConstant d q ad bd Cfr a rho c0 Cs := by
  unfold finePairFieldFactorialConstant fieldTailConstant poissonCountWeight
  positivity [finePairUniformSpatialPrefactor_nonneg d q ad bd Cfr a rho c0]

theorem paperRegimePairFieldConstant_ge_one {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr Cs : ℝ) (q : ℕ) :
    1 ≤ paperRegimePairFieldConstant C Q Cfr Cs q := by
  unfold paperRegimePairFieldConstant
  linarith [finePairFieldFactorialConstant_nonneg d q C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (densityIntervalExponent C.densityLower C.densityUpper+1) (3*Cs)]

theorem paperRegimePairAliasConstant_ge_one {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr Cs : ℝ) (q : ℕ) (hCs : 0 ≤ Cs) :
    1 ≤ paperRegimePairAliasConstant C Q Cfr Cs q := by
  unfold paperRegimePairAliasConstant finePairSaddleAliasFactorialConstant
  apply aliasTailConstant_ge_one
  · positivity [finePairUniformSpatialPrefactor_nonneg d q C.densityLower C.densityUpper Cfr Q.a Q.ρ
      (densityIntervalExponent C.densityLower C.densityUpper+1),spatialInverseFourConstant_nonneg d]
  · positivity
  · positivity [finePairAliasGeometricBase_nonneg d C.densityUpper]

theorem paperLowerRegime_uniform_pair_norms {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr Cs : ℝ) (hK : 1 ≤ K) (hCfr : 1 ≤ Cfr) (hCs : 0 ≤ Cs) (q : ℕ) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M  →  ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta  →  ∀ (F : ℕ → ℕ)
      (w : ∀ n : ℕ, (Fin n → Covariate d) → Fin n → ℝ),
      (∀ n i, Measurable (fun U => w n U i))  →  (∀ n U i, |w n U i| ≤ 1)  → 
      let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
      let ell := N*Real.exp (-c0*(D : ℝ))
      let ad := C.densityLower+(M : ℝ)⁻¹
      let bd := C.densityUpper-(M : ℝ)⁻¹
      (∀ n : ℕ, 1 ≤ n  →  ∀ b : Bool,
        Integrable (finePairNuisanceEnergy (F := F n) b ad bd ell N M q Cfr Q.a Q.ρ Q.v eta (w n))
          (fullSpatialPatchDesign d n)) ∧
      (∀ n : ℕ, 3 ≤ n  →  n ≤ M  →  ∀ U,
        finePairNuisanceEnergy (F := F n) false ad bd ell N M q Cfr Q.a Q.ρ Q.v eta (w n) U=0) ∧
      (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
        ∫ U, finePairNuisanceEnergy (F := F (3+j)) false ad bd ell N M q Cfr Q.a Q.ρ Q.v eta (w (3+j)) U
          ∂fullSpatialPatchDesign d (3+j))  ≤ 
        paperRegimePairAliasConstant C Q Cfr Cs q*
          (eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*N^(4-(d : ℝ)))*
          poissonCountWeight (paperRegimePairAliasConstant C Q Cfr Cs q*mu) (M+1) ∧
      (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
        ∫ U, finePairNuisanceEnergy (F := F (3+j)) true ad bd ell N M q Cfr Q.a Q.ρ Q.v eta (w (3+j)) U
          ∂fullSpatialPatchDesign d (3+j))  ≤ 
        paperRegimePairFieldConstant C Q Cfr Cs q*eta^4*
          Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*mu^4*ell^(4-2*(d : ℝ)) ∧
      paperRegimePairFieldConstant C Q Cfr Cs q*eta^4*
          Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*mu^4*ell^(4-2*(d : ℝ))  ≤ 
        paperRegimePairFieldConstant C Q Cfr Cs q*eta^4*mu^2*N^(-(d : ℝ)) := by
  have hdpos : 0 < d := by omega
  have hab : C.densityLower < C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let A := paperLowerRegimeDegreeSlope d+1
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  have hA : 0 ≤ A := by dsimp [A]; linarith [paperLowerRegimeDegreeSlope_positive d]
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_hierarchy hdpos C Q K c0 1 1 hK hc0 (by norm_num) (by norm_num)
  obtain ⟨M2,hM2⟩ := paperLowerRegime_uniform_field_scale (by omega : 4 < d) C Q K hK
  have hevent : ∀ᶠ M : ℕ in atTop, M1 ≤ M ∧ M2 ≤ M ∧ 2 ≤ M ∧
      highCenterResolutionThreshold C ≤ (M : ℝ) ∧
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 := by
    filter_upwards [eventually_ge_atTop M1,eventually_ge_atTop M2,eventually_ge_atTop (2 : ℕ),
      eventually_ge_atTop (Nat.ceil (highCenterResolutionThreshold C)),
      shrunkDensityExponent_eventually_le_plus_one C.densityLower_pos hab]
      with M h1 h2 hp hr ht
    exact ⟨h1,h2,hp,(Nat.le_ceil _).trans (by exact_mod_cast hr),ht⟩
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hevent
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R F w hw hwb
  obtain ⟨h1,h2,hm2,hres,htau⟩ := hM0 M hm
  have H := hM1 M D h1 N mu eta R
  let ell := N*Real.exp (-c0*(D : ℝ))
  have hell : 0 < ell := zero_lt_one.trans_le H.cutoff.le
  have hN : 0 < N := zero_lt_one.trans_le R.scale
  have hellN : ell ≤ N := by
    have he : Real.exp (-c0*(D : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D])
    exact (mul_le_mul_of_nonneg_left he hN.le).trans_eq (mul_one N)
  obtain ⟨had,habM⟩ := high_source_interval_numeric C (M : ℝ) hres
  have had' : 0 < C.densityLower+(M : ℝ)⁻¹ := by simpa only [one_div] using had
  have hab' : C.densityLower+(M : ℝ)⁻¹ < C.densityUpper-(M : ℝ)⁻¹ := by simpa only [one_div] using habM
  have hinv : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have hamin : C.densityLower ≤ C.densityLower+(M : ℝ)⁻¹ := by linarith
  have hbmax : C.densityUpper-(M : ℝ)⁻¹ ≤ C.densityUpper := by linarith
  have htauEq : exteriorTau (((C.densityLower+(M : ℝ)⁻¹)+(C.densityUpper-(M : ℝ)⁻¹))/
      ((C.densityUpper-(M : ℝ)⁻¹)-(C.densityLower+(M : ℝ)⁻¹))) =
      shrunkDensityExponent C.densityLower C.densityUpper M := by
    rw [exteriorTau_sqrt_ratio _ _ had' hab']
    rfl
  have htau' : exteriorTau (((C.densityLower+(M : ℝ)⁻¹)+(C.densityUpper-(M : ℝ)⁻¹))/
      ((C.densityUpper-(M : ℝ)⁻¹)-(C.densityLower+(M : ℝ)⁻¹))) ≤ c0 := by rw [htauEq]; exact htau
  have htaunonneg : 0 ≤ shrunkDensityExponent C.densityLower C.densityUpper M :=
    (densityIntervalExponent_pos had' hab').le
  have hD : 3 ≤ D := by
    have hmr : (2 : ℝ) ≤ M := by exact_mod_cast hm2
    have hslope : 2 ≤ paperLowerRegimeDegreeSlope d := by
      unfold paperLowerRegimeDegreeSlope
      linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have hdr : (3 : ℝ) ≤ D := by nlinarith [R.degree_lower]
    exact_mod_cast hdr
  have hi (n : ℕ) (hn : 1 ≤ n) (b : Bool) := finePairNuisanceEnergy_integrable_and_bound (F := F n)
    hd C Q b _ _ ell N had' hab' hell hellN M q hn Cfr eta hCfr R.amplitude_positive.le
    R.amplitude_half (w n) (hw n) (hwb n)
  refine ⟨fun n hn b => (hi n hn b).1,?_,?_,?_,?_⟩
  · intro n hn hnM U
    exact finePairAliasNuisanceEnergy_zero_selected_count C Q _ _ ell N had' hab'
      M q hn hnM Cfr eta hCfr (w n) U
  · have ha := finite_fine_pair_alias_nuisance_energy_le hd C Q C.densityLower_pos hamin hbmax hab'
      htau' hc0 hA M q Cfr eta ell N Cs mu hCfr R.amplitude_positive.le R.amplitude_half
      hN rfl H.cutoff.le hellN (R.degree_linear H.resolution) hCs R.occupancy_positive.le
      R.occupancy_small.le F w hw hwb
    apply ha.trans
    have hCal : 0 ≤ paperRegimePairAliasConstant C Q Cfr Cs q :=
      zero_le_one.trans (paperRegimePairAliasConstant_ge_one C Q Cfr Cs q hCs)
    have he : 1 ≤ Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ)) :=
      Real.one_le_exp (by positivity)
    have h := mul_le_mul_of_nonneg_left he
      (show 0 ≤ paperRegimePairAliasConstant C Q Cfr Cs q*eta^4*N^(4-(d : ℝ))*
        poissonCountWeight (paperRegimePairAliasConstant C Q Cfr Cs q*mu) (M+1) by
        positivity [poissonCountWeight_nonneg (mul_nonneg hCal R.occupancy_positive.le) (M+1)])
    convert h using 1  <;> dsimp [paperRegimePairAliasConstant,A,c0]  <;> ring
  · have hf := finite_fine_field_nuisance_energy_le hd hD C Q C.densityLower_pos hamin hbmax hab'
      htau' M q Cfr eta ell N Cs mu hCfr R.amplitude_positive.le R.amplitude_half
      hell hellN hCs R.occupancy_positive.le R.occupancy_small.le F w hw hwb
    rw [htauEq] at hf
    apply hf.trans
    have hC : finePairFieldFactorialConstant d q C.densityLower C.densityUpper Cfr Q.a Q.ρ c0 (3*Cs) ≤ 
        paperRegimePairFieldConstant C Q Cfr Cs q := by
      unfold paperRegimePairFieldConstant
      linarith
    have hp : (ell^(2-(d : ℝ)))^2=ell^(4-2*(d : ℝ)) := by
      rw [← Real.rpow_mul_natCast hell.le]
      congr 1
      ring
    have h := mul_le_mul_of_nonneg_right hC
      (show 0 ≤ eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*
        mu^4*ell^(4-2*(d : ℝ)) by positivity)
    rw [hp]
    convert h using 1  <;> ring
  · have hCf : 0 ≤ paperRegimePairFieldConstant C Q Cfr Cs q :=
      zero_le_one.trans (paperRegimePairFieldConstant_ge_one C Q Cfr Cs q)
    have h := mul_le_mul_of_nonneg_left (hM2 M D h2 N mu eta R).1
      (show 0 ≤ paperRegimePairFieldConstant C Q Cfr Cs q*eta^4 by positivity)
    convert h using 1 <;> ring

end NearlyMinimax
