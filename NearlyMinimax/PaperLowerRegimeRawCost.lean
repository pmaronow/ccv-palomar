module

public import NearlyMinimax.PaperLowerRegimeInfiniteEnergy
public import NearlyMinimax.PaperLowerRegimeCenteredActivity
public import NearlyMinimax.RawCostAlgebra


@[expose] public section

/-! The manuscript's complete raw-cost inequality for every tuple in
Reg(K). The energy is the actual infinite series of literal nuisance
norms, and the activity is the actual balanced reference mark budget. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local irreducible] sourceRowData highRowTotalMass

 def paperRegimeCenteredActivity {d : ℕ} (C : ModelConstants d)
    (Cfr : ℝ) (M D : ℕ) (N mu : ℝ) (k : ℕ) : ℝ :=
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let ell := N*Real.exp (-c0*D)
  highRowTotalMass (completeSourceRows C k D M
    (lowerSaddleResponseOrder C.smoothness d) Cfr (spatialInterpolationLambda d) ell N mu).rowMass/
      highCenterMix C

 def paperRegimeRawCostConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K Cfr Cs cf : ℝ) : ℝ :=
  rawCostConstant
    (paperRegimeLocalActivityConstant C Cfr (spatialInterpolationLambda d)
      (lowerSaddleResponseOrder C.smoothness d))
    (paperRegimeCompleteDefectConstant C Q Cfr Cs)
    (paperRegimeCompleteAliasConstant C Q K Cfr Cs)
    (paperRegimeCompleteFieldConstant C Q Cfr Cs) cf
    (paperRegimeCompleteExteriorConstant C Q Cs)

 theorem paperRegimeRawCostConstant_ge_one {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K Cfr Cs cf : ℝ) :
    1 ≤ paperRegimeRawCostConstant C Q K Cfr Cs cf := rawCostConstant_ge_one _ _ _ _ _ _

 theorem paperLowerRegime_uniform_raw_cost {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr Cs cf : ℝ) (hK : 1 ≤ K) (hCfr : 1 ≤ Cfr) (hCs : 0 ≤ Cs) (hcf : 0 ≤ cf) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ k : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ n h : ℝ, 0 ≤ n → 0 < h → mu = n*h^(d : ℝ) → eta = cf*h^C.smoothness →
      let Bl := paperRegimeCenteredActivity C Cfr M D N mu k
      let B := N^2*Real.exp (shrunkDensityExponent C.densityLower C.densityUpper M*M)
      let CG := paperRegimeRawCostConstant C Q K Cfr Cs cf
      1+Bl^2+h^(-(d : ℝ))*paperRegimeLocalEnergy C Q Cfr Cs M D N mu eta ≤
        CG*(B^2+n^2*h^((d : ℝ)+4*C.smoothness)*N^(-(d : ℝ))+
          n*h^(4*C.smoothness)*(Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M)*
            N^(4-(d : ℝ)))*(CG*mu)^M/(M+1).factorial+
          n*h^(4*C.smoothness)*B^2*(CG*mu)^D/(D+1).factorial) := by
  let q := lowerSaddleResponseOrder C.smoothness d
  let lam := spatialInterpolationLambda d
  let CB := paperRegimeLocalActivityConstant C Cfr lam q
  let C5 := paperRegimeCompleteDefectConstant C Q Cfr Cs
  let C6 := paperRegimeCompleteAliasConstant C Q K Cfr Cs
  let C7 := paperRegimeCompleteFieldConstant C Q Cfr Cs
  let ch := paperRegimeCompleteExteriorConstant C Q Cs
  have hq : 1 ≤ q := by dsimp only [q,lowerSaddleResponseOrder]; omega
  obtain ⟨Me,hMe⟩ := paperLowerRegime_uniform_local_norm_infinite_energy hd C Q K Cfr Cs hK hCfr hCs
  obtain ⟨Ma,hMa⟩ := paperLowerRegime_uniform_centered_activity C Q K Cfr lam hK hCfr q hq
  obtain ⟨Ms,hMs⟩ := paperLowerRegime_uniform_source_guards C Q K Cfr lam hK hCfr q hq
  let M0 := max Me (max Ma Ms)
  refine ⟨M0,?_⟩
  intro M D hm N mu eta Reg k hk0 horder hk n h hn hh hmu heta
  letI := hk0
  letI := horder
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let ell := N*Real.exp (-c0*D)
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let Bl := paperRegimeCenteredActivity C Cfr M D N mu k
  let B := N^2*Real.exp (shrunkDensityExponent C.densityLower C.densityUpper M*M)
  have hme : Me ≤ M := (le_max_left _ _).trans hm
  have hma : Ma ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hms : Ms ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have GS := (hMs M D hms N mu eta Reg k).1
  have hmass : 0 ≤ highRowTotalMass R.rowMass := GS.total_positive.le
  have hBl : 0 ≤ Bl := div_nonneg hmass (highCenterMix_mem C).1.le
  have hrow : highRowTotalMass R.rowMass ≤ Bl := by
    apply (le_div_iff₀ (highCenterMix_mem C).1).mpr
    exact mul_le_of_le_one_right hmass (highCenterMix_mem C).2.le
  have hcost : Bl ≤ CB*B := by
    convert (hMa M D hma N mu eta Reg k).1 using 1 <;> (try dsimp only [Bl,paperRegimeCenteredActivity,CB,B,q,lam]) <;> ring
  have hE := (hMe M D hme N mu eta Reg k hk0 horder hk Bl hrow).2
  have htau : 0 ≤ shrunkDensityExponent C.densityLower C.densityUpper M := by
    obtain ⟨ha,hab⟩ := high_source_interval_numeric C (M : ℝ) GS.resolution
    unfold shrunkDensityExponent
    simpa only [one_div] using (densityIntervalExponent_pos ha hab).le
  have hB : 1 ≤ B := by
    simpa only [one_mul,B] using mul_le_mul
      (show (1 : ℝ) ≤ N^2 from one_le_pow₀ Reg.scale)
      (Real.one_le_exp_iff.mpr (mul_nonneg htau (Nat.cast_nonneg M)))
      (by norm_num) (by positivity)
  have he4 : eta^4 = cf^4*h^(4*C.smoothness) := by
    rw [heta,mul_pow,← Real.rpow_mul_natCast hh.le]
    congr 1
    congr 1
    ring
  have hCB : 0 ≤ CB := (paperRegimeLocalActivityConstant_pos C Cfr lam q).le
  have hC5 : 0 ≤ C5 := (completeGeometryDefectConstant_pos _ _ _ _ _ _ _).le
  have hC6 : 0 ≤ C6 := (completeGeometryAliasConstant_pos _ _ _ _ _ _ _ _ _ _ _).le
  have hC7 : 0 ≤ C7 := (completeGeometryFieldConstant_pos _ _ _ _ _ _ _ _ _).le
  have hch : 0 ≤ ch := (completeGeometryExteriorConstant_pos _ _ _).le
  have hE' : paperRegimeLocalEnergy C Q Cfr Cs M D N mu eta ≤
      3*(C5+C7)*eta^4*mu^2*N^(-(d : ℝ))+
      3*C6*eta^4*(Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M)*N^(4-(d : ℝ)))*
        (C6*mu)^(M+1)/(M+1).factorial+
      Real.exp ch*eta^4*(Bl+1)^2*(ch*mu)^(D+1)/(D+1).factorial := by
    simpa only [paperRegimeCompleteEnergyBound,poissonCountWeight,mul_div_assoc] using hE
  have hr := raw_energy_cost_bound (n := n) (v := h^(d : ℝ)) (mu := mu) (eta4 := eta^4)
    (h4s := h^(4*C.smoothness)) (B := B) (Bl := Bl)
    (E := paperRegimeLocalEnergy C Q Cfr Cs M D N mu eta)
    (Fdef := N^(-(d : ℝ)))
    (Fal := Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M)*N^(4-(d : ℝ)))
    (CB := CB) (C5 := C5) (C6 := C6) (C7 := C7) (cf := cf) (ch := ch)
    (Real.rpow_pos_of_pos hh _) hmu hn (Real.rpow_nonneg hh.le _) he4 hB hBl hCB hC5 hC6 hC7 hcf hch
    (Real.rpow_nonneg (zero_lt_one.trans_le Reg.scale).le _)
    (by positivity [zero_lt_one.trans_le Reg.scale]) hcost M D hE'
  dsimp only at hr ⊢
  rw [Real.rpow_neg hh.le]
  have hp : h^(d : ℝ)*h^(4*C.smoothness) = h^((d : ℝ)+4*C.smoothness) :=
    (Real.rpow_add hh _ _).symm
  rw [← hp]
  convert hr using 1 <;> dsimp only [paperRegimeRawCostConstant,CB,C5,C6,C7,ch,q,lam] <;> ring

end NearlyMinimax
