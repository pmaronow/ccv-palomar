module

public import NearlyMinimax.PaperLowerRegimeAliasTail
public import NearlyMinimax.PaperLowerRegimeFieldScale
public import NearlyMinimax.CompleteGeometryEnergyAssembly


@[expose] public section

/-! Genuine complete-source geometry and finite factorial energy, uniformly
on every tuple in Reg(K), without restricting to a saddle sequence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

 def paperRegimeCompleteGeometryEnvelope {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K Cfr Bl : ℝ) (M D : ℕ)
    (N mu eta : ℝ) (n : ℕ) (U : Fin n → Covariate d) : ℝ :=
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  completeSourceGeometryEnvelope D M (paperRegimeFineTargetBound d K c0)
    (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper c0
    (N*Real.exp (-c0*D)) N mu Cfr Q.a Q.ρ eta
    (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) Bl n U

 def paperRegimeCompleteDefectConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr Cs : ℝ) : ℝ :=
  completeGeometryDefectConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityUpper Cfr Q.a Q.ρ Cs
 def paperRegimeCompleteFieldConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr Cs : ℝ) : ℝ :=
  completeGeometryFieldConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (densityIntervalExponent C.densityLower C.densityUpper+1) Cs
 def paperRegimeCompleteAliasConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K Cfr Cs : ℝ) : ℝ :=
  completeGeometryAliasConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (densityIntervalExponent C.densityLower C.densityUpper+1) (paperLowerRegimeDegreeSlope d+1) Cs
    (paperRegimeAliasFactorialConstant C K Cfr Q.a Q.ρ Cs (lowerSaddleResponseOrder C.smoothness d))
 def paperRegimeCompleteExteriorConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cs : ℝ) : ℝ :=
  completeGeometryExteriorConstant d Cs (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)

 def paperRegimeCompleteEnergyBound {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K Cfr Cs Bl : ℝ) (M D : ℕ) (N mu eta : ℝ) : ℝ :=
  let C5 := paperRegimeCompleteDefectConstant C Q Cfr Cs
  let C6 := paperRegimeCompleteAliasConstant C Q K Cfr Cs
  let C7 := paperRegimeCompleteFieldConstant C Q Cfr Cs
  let ch := paperRegimeCompleteExteriorConstant C Q Cs
  3*(C5+C7)*eta^4*mu^2*N^(-(d : ℝ))+
    3*C6*eta^4*(Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M)*N^(4-(d : ℝ)))*
      poissonCountWeight (C6*mu) (M+1)+
    Real.exp ch*eta^4*(Bl+1)^2*poissonCountWeight (ch*mu) (D+1)

 theorem paperRegimeCompleteGeometryEnvelope_nonneg {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (K Cfr Bl : ℝ) (M D : ℕ)
    (N mu eta : ℝ) (n : ℕ) (U : Fin n → Covariate d) :
    0 ≤ paperRegimeCompleteGeometryEnvelope C Q K Cfr Bl M D N mu eta n U :=
  completeSourceGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

 theorem paperLowerRegime_uniform_complete_geometry_energy {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr Cs : ℝ) (hK : 1 ≤ K) (hCs : 0 ≤ Cs) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0 ≤ M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ Bl : ℝ,
      (∀ r, Integrable (paperRegimeCompleteGeometryEnvelope C Q K Cfr Bl M D N mu eta r)
        (fullSpatialPatchDesign d r)) ∧
      ∀ J : ℕ, (∑ r ∈ Finset.range (J+1), poissonCountWeight (Cs*mu) r *
        ∫ U, paperRegimeCompleteGeometryEnvelope C Q K Cfr Bl M D N mu eta r U
          ∂fullSpatialPatchDesign d r) ≤ paperRegimeCompleteEnergyBound C Q K Cfr Cs Bl M D N mu eta := by
  let q := lowerSaddleResponseOrder C.smoothness d
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let A := paperLowerRegimeDegreeSlope d+1
  let Rt := paperRegimeFineTargetBound d K c0
  let Cord := paperRegimeAliasFactorialConstant C K Cfr Q.a Q.ρ Cs q
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hc0 : 0 ≤ c0 := by dsimp [c0]; linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  have hA : 0 ≤ A := by dsimp [A]; linarith [paperLowerRegimeDegreeSlope_positive d]
  have hOrdConst : 0 ≤ Cord := zero_le_one.trans (paperRegimeAliasFactorialConstant_ge_one C K Cfr Q.a Q.ρ Cs q hCs)
  obtain ⟨Ma,hMa⟩ := paperLowerRegime_uniform_alias_factorial_tail hd C Q K Cfr Q.a Q.ρ Cs hK hCs q
  obtain ⟨Mf,hMf⟩ := paperLowerRegime_uniform_field_scale (by omega) C Q K hK
  obtain ⟨Mh,hMh⟩ := paperLowerRegime_uniform_hierarchy (NeZero.pos d) C Q K c0 1 1 hK hc0 (by norm_num) (by norm_num)
  have hevent : ∀ᶠ M : ℕ in atTop, Ma ≤ M ∧ Mf ≤ M ∧ Mh ≤ M ∧ 2 ≤ M ∧
      highCenterResolutionThreshold C ≤ (M : ℝ) ∧ shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 := by
    filter_upwards [eventually_ge_atTop Ma,eventually_ge_atTop Mf,eventually_ge_atTop Mh,
      eventually_ge_atTop (2 : ℕ),eventually_ge_atTop (Nat.ceil (highCenterResolutionThreshold C)),
      shrunkDensityExponent_eventually_le_plus_one C.densityLower_pos hab] with M ha hf hh hm hr ht
    exact ⟨ha,hf,hh,hm,(Nat.le_ceil _).trans (by exact_mod_cast hr),ht⟩
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp hevent
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R Bl
  obtain ⟨hma,hmf,hmh,hm2,hres,htau⟩ := hM0 M hm
  have H := hMh M D hmh N mu eta R
  let ell := N*Real.exp (-c0*D)
  have hell : 1 ≤ ell := H.cutoff.le
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one R.scale
  have hellN : ell ≤ N := by
    have he : Real.exp (-c0*D) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D])
    exact (mul_le_mul_of_nonneg_left he hN.le).trans_eq (mul_one N)
  have hD : 3 ≤ D := by
    have hmR : (2 : ℝ) ≤ M := by exact_mod_cast hm2
    have hdSlope : 2 ≤ paperLowerRegimeDegreeSlope d := by unfold paperLowerRegimeDegreeSlope; linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have hh := R.degree_lower
    have hDreal : (3 : ℝ) ≤ D := by nlinarith only [hmR,hdSlope,hh]
    exact_mod_cast hDreal
  have hshrink : C.densityLower+(M : ℝ)⁻¹ < C.densityUpper-(M : ℝ)⁻¹ := by
    simpa only [one_div] using (high_source_interval_numeric C (M : ℝ) hres).2
  have hAD : 0 < C.densityLower+(M : ℝ)⁻¹ := add_pos_of_pos_of_nonneg C.densityLower_pos (by positivity)
  have hext : exteriorTau (((C.densityLower+(M : ℝ)⁻¹)+(C.densityUpper-(M : ℝ)⁻¹))/
      ((C.densityUpper-(M : ℝ)⁻¹)-(C.densityLower+(M : ℝ)⁻¹))) =
      shrunkDensityExponent C.densityLower C.densityUpper M := by
    simpa only [shrunkDensityExponent,densityIntervalExponent,one_div] using exteriorTau_sqrt_ratio _ _ hAD hshrink
  have hfield : Real.exp (2*exteriorTau (((C.densityLower+(M : ℝ)⁻¹)+(C.densityUpper-(M : ℝ)⁻¹))/
      ((C.densityUpper-(M : ℝ)⁻¹)-(C.densityLower+(M : ℝ)⁻¹)))*M)*(ell^(2-(d : ℝ)))^2*mu^4 ≤
      mu^2*N^(-(d : ℝ)) := by
    rw [hext]
    convert (hMf M D hmf N mu eta R).2 using 1 <;> ring
  have hbd : 0 ≤ C.densityUpper-(M : ℝ)⁻¹ := hAD.le.trans hshrink.le
  have hbdB : C.densityUpper-(M : ℝ)⁻¹ ≤ C.densityUpper := sub_le_self _ (by positivity)
  have hAlias := hMa M D hma N mu eta R (fun _ => D)
  have hoI (r : ℕ) := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (d := d) (n := r) (F := D)
    hd (ordinaryFineAliasTargetSet d D ell N mu) M Rt q C.densityLower C.densityUpper c0 Cfr Q.a Q.ρ eta ell
    (fun t => higherBandTargetScale d t N mu) hell (fun t ht => by
      have h := (Finset.mem_filter.mp ht).2
      exact ⟨by omega,h.2.le⟩)
  have hOrd : (∑ j ∈ Finset.range (D-M), poissonCountWeight (Cs*mu) (M+1+j)*
      ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := M+1+j) (F := D)
        (ordinaryFineAliasTargetSet d D ell N mu) M Rt q C.densityLower C.densityUpper c0 Cfr Q.a Q.ρ eta ell
        (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (M+1+j)) ≤
      Cord*(eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M)*N^(4-(d : ℝ)))*
        poissonCountWeight (Cord*mu) (M+1) := by
    apply le_trans (Finset.sum_le_sum (fun j hj => ?_)) (hAlias.2 (D-M))
    apply mul_le_mul_of_nonneg_left _ (poissonCountWeight_nonneg (mul_nonneg hCs R.occupancy_positive.le) _)
    apply integral_mono (hoI (M+1+j)) (hAlias.1 (M+1+j))
    intro U
    have ho := ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg (F := D)
      (ordinaryFineAliasTargetSet d D ell N mu) M Rt q C.densityLower C.densityUpper c0 Cfr Q.a Q.ρ eta ell
      (fun t => higherBandTargetScale d t N mu) U
    have hp := finePairAliasGeometryEnvelope_nonneg (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹)
      ell N M q Cfr Q.a Q.ρ eta U
    change _ ≤ 2*(_+_)
    nlinarith only [ho,hp]
  have hhigher := finite_complete_higher_geometry_energy_le hd hD C.densityLower C.densityUpper c0 A ell N mu
    M Rt q Cfr Q.a Q.ρ eta Cs _ C.densityLower_pos Q.a_pos hshrink (hext.trans_le htau) hc0 hA hCs
    hell hellN rfl (R.degree_linear (by omega)) R.occupancy_positive R.occupancy_small.le H.base
    R.response_remainder hfield hOrd
  have hCal : 0 ≤ finePairSaddleAliasFactorialConstant d q C.densityLower C.densityUpper Cfr Q.a Q.ρ c0 A (3*Cs) := by
    unfold finePairSaddleAliasFactorialConstant aliasTailConstant
    have hP := finePairUniformSpatialPrefactor_nonneg d q C.densityLower C.densityUpper Cfr Q.a Q.ρ c0
    have hI := spatialInverseFourConstant_nonneg d
    have hB := finePairAliasGeometricBase_nonneg d C.densityUpper
    positivity
  refine ⟨?_,?_⟩
  · intro r
    exact completeSourceGeometryEnvelope_integrable (n := r) hd D M Rt q C.densityLower C.densityUpper c0 ell N mu Cfr
      Q.a Q.ρ eta _ Bl hell hellN
  · intro J
    have htau0 : 0 ≤ shrunkDensityExponent C.densityLower C.densityUpper M := by
      unfold shrunkDensityExponent
      exact (densityIntervalExponent_pos hAD hshrink).le
    have h := completeSourceGeometryEnvelope_factorial_from_higher (NeZero.pos d) D M Rt q J hD
      C.densityLower C.densityUpper c0 A ell N mu Cfr Q.a Q.ρ eta
      (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) Bl Cs Cord
      (shrunkDensityExponent C.densityLower C.densityUpper M) hN hCs R.occupancy_positive.le R.occupancy_small.le
      hbd hbdB hOrdConst hCal htau0 hhigher
    exact h

end NearlyMinimax
