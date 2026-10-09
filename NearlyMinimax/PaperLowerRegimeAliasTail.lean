module

public import NearlyMinimax.PaperLowerRegimeAliasEnvelope
public import NearlyMinimax.AliasTailSummation


@[expose] public section

/-! The true ordinary-plus-pair spatial alias tail, uniformly over all
tuples in the paper's Reg(K). The factorial constant is fixed before every
resolution, degree, scale, occupancy, amplitude and response/frame count. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def paperRegimeAliasFactorialConstant {d : ℕ} (C : ModelConstants d)
    (K Cfr a rho Cs : ℝ) (q : ℕ) : ℝ :=
  aliasTailConstant (paperRegimeAliasSpatialPrefactor C K Cfr a rho q) Cs
    (paperRegimeAliasSpatialBase C) (paperRegimeAliasSpatialExponent C K)

theorem paperRegimeAliasFactorialConstant_ge_one {d : ℕ} (C : ModelConstants d)
    (K Cfr a rho Cs : ℝ) (q : ℕ) (hCs : 0 ≤ Cs) :
    1 ≤ paperRegimeAliasFactorialConstant C K Cfr a rho Cs q :=
  aliasTailConstant_ge_one (paperRegimeAliasSpatialPrefactor_nonneg C K Cfr a rho q)
    hCs (paperRegimeAliasSpatialBase_nonneg C)

theorem paperLowerRegime_uniform_alias_factorial_tail {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr a rho Cs : ℝ) (hK : 1 ≤ K) (hCs : 0 ≤ Cs) (q : ℕ) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ (F : ℕ → ℕ),
      (∀ n : ℕ, Integrable
        (paperRegimeAliasGeometryEnvelope C K Cfr a rho M D q n (F n) N mu eta)
        (fullSpatialPatchDesign d n)) ∧
      ∀ J : ℕ,
      (∑ j ∈ Finset.range J, poissonCountWeight (Cs*mu) (M+1+j) *
        ∫ U, paperRegimeAliasGeometryEnvelope C K Cfr a rho M D q (M+1+j) (F (M+1+j)) N mu eta U
          ∂fullSpatialPatchDesign d (M+1+j)) ≤
      paperRegimeAliasFactorialConstant C K Cfr a rho Cs q *
        (eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*
          N^(4-(d : ℝ))) *
        poissonCountWeight (paperRegimeAliasFactorialConstant C K Cfr a rho Cs q*mu) (M+1) := by
  have hdpos : 0 < d := by omega
  have hab : C.densityLower < C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_hierarchy hdpos C Q K c0 1 1
    hK hc0 (by norm_num) (by norm_num)
  have hevent : ∀ᶠ M : ℕ in atTop,
      M1 ≤ M ∧ highCenterResolutionThreshold C ≤ (M : ℝ) ∧
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 := by
    filter_upwards [eventually_ge_atTop M1,
      eventually_ge_atTop (Nat.ceil (highCenterResolutionThreshold C)),
      shrunkDensityExponent_eventually_le_plus_one C.densityLower_pos hab]
      with M hm hc ht
    exact ⟨hm,(Nat.le_ceil _).trans (by exact_mod_cast hc),ht⟩
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hevent
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R F
  obtain ⟨hm1,hres,htau⟩ := hM0 M hm
  have H := hM1 M D hm1 N mu eta R
  have he (n : ℕ) := paperLowerRegime_alias_geometry_integrable_and_bound hd C Q
    K Cfr a rho M D q N mu eta R H hres htau n (F n)
  refine ⟨fun n => (he n).1,?_⟩
  intro J
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one R.scale
  exact finite_alias_energy_tail_le
    (paperRegimeAliasSpatialPrefactor_nonneg C K Cfr a rho q)
    (by positivity : 0 ≤ eta^4*Real.exp
      (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*N^(4-(d : ℝ)))
    hCs (paperRegimeAliasSpatialBase_nonneg C)
    (paperRegimeAliasSpatialExponent_nonneg hd C K) R.occupancy_positive.le R.occupancy_small.le
    M J (fun n => ∫ U, paperRegimeAliasGeometryEnvelope C K Cfr a rho M D q n (F n) N mu eta U
      ∂fullSpatialPatchDesign d n) (fun j hj => (he (M+1+j)).2)

end NearlyMinimax
