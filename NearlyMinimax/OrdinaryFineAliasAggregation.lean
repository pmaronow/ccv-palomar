module

public import NearlyMinimax.OrdinaryFineAliasSpatialEnergy


@[expose] public section

/-! Finite aggregation of the genuine all-count ordinary fine aliases.
The source's actual target scales and rounded saddle supply the guards. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def ordinaryFineAliasTargetSet (d D : ℕ) (L N mu : ℝ) : Finset ℕ :=
  (Finset.range (D+1)).filter (fun r => 3 ≤ r ∧ L < higherBandTargetScale d r N mu)

/-- Every actual selected fine ordinary row belongs to the displayed target
set. Zero-variation rows may still occur in the set and contribute zero. -/
theorem higherBandFamily_fine_target_mem {d D M q : ℕ} {ad bd C lam L N mu : ℝ}
    (i : HigherBandFamilyIndex d D M q ad bd C lam L N mu) (hi : i.val.2 = true) :
    higherBandFamilyTarget i.val ∈ ordinaryFineAliasTargetSet d D L N mu := by
  have hD : higherBandFamilyTarget i.val ≤ D := by
    unfold higherBandFamilyTarget
    have h := i.val.1.isLt
    omega
  unfold ordinaryFineAliasTargetSet
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    ⟨by unfold higherBandFamilyTarget; omega, i.property.2.1 hi⟩⟩

def ordinaryFineAliasFamilyRawAction {d n F : ℕ} (I : Finset ℕ)
    (ad bd lam L : ℝ) (T : ℕ → ℝ) (M q : ℕ) (C a V eta : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∑ r ∈ I, ordinaryFineAliasRawAction ad bd lam L (T r) M r q C a V eta U p g w c y

def ordinaryAliasFamilySpatialPrefactor (d q R : ℕ) (ad bd c0 C a rho : ℝ) : ℝ :=
  ((R+1 : ℕ) : ℝ)^2 * ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho

theorem ordinaryAliasFamilySpatialPrefactor_nonneg (d q R : ℕ) (ad bd c0 C a rho : ℝ) :
    0 ≤ ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho :=
  mul_nonneg (sq_nonneg _) (ordinaryAliasSpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)

/-- Finite alias aggregation, with genuine full spatial integration and the
actual sum over all ternary responses. The tuple-dependent nuisance guards
are uniform across rows; no energy inequality is assumed. -/
theorem ordinaryFineAliasFamilyRawAction_spatial_response_energy_le {d n F M R : ℕ}
    (hd : 5 ≤ d) (I : Finset ℕ) (ad bd c0 D K N : ℝ) (T : ℕ → ℝ)
    (haD : 0 < ad) (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0)
    (hI : ∀ r ∈ I, 2 ≤ r ∧ r ≤ R)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M)
    (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M)
    (hLT : ∀ r ∈ I, N*Real.exp (-c0*D) ≤ T r)
    (q : ℕ) (hn : 1 ≤ n) (C a V eta rho : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho) (hetarho : eta ≤ rho/2)
    (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hpmeas : ∀ i, Measurable (fun U => p U i))
    (hgmeas : ∀ i, Measurable (fun U => g U i))
    (hwmeas : ∀ i, Measurable (fun U => w U i))
    (c : (Fin n → Covariate d) → HighFrameIndex d F → ℝ)
    (hcmeas : ∀ gamma, Measurable (fun U => c U gamma))
    (hpD : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i,
      p U i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |g U i| ≤ rho/2)
    (hw : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |w U i| ≤ 1)
    (hc : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∑ gamma, |c U gamma| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, ∫ U,
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) (N*Real.exp (-c0*D)) T M q C a V eta U
        (p U) (g U) (w U) (c U) y^2 ∂fullSpatialPatchDesign d n) ≤
      ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho *
        eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialResponseBase d bd)^n := by
  have hbd : 0 ≤ bd := by
    have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
    linarith
  have hsub : I ⊆ Finset.range (R+1) := fun r hr => Finset.mem_range.mpr (by have := (hI r hr).2; omega)
  have hcard : (I.card : ℝ)^2 ≤ ((R+1 : ℕ) : ℝ)^2 := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact_mod_cast Nat.pow_le_pow_left h 2
  let B := ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho *
    eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
      Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have := ordinaryAliasSpatialPrefactor_nonneg d q R ad bd c0 C a rho
    unfold ordinaryAliasSpatialCountBase
    positivity
  have hsum (y : Fin n → Fin 3) :
      (∫ U, ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) (N*Real.exp (-c0*D)) T M q C a V eta U
        (p U) (g U) (w U) (c U) y^2 ∂fullSpatialPatchDesign d n) ≤ ((R+1 : ℕ) : ℝ)^2*B := by
    let f := fun r (U : Fin n → Covariate d) => ordinaryFineAliasRawAction
      (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
      (N*Real.exp (-c0*D)) (T r) M r q C a V eta U (p U) (g U) (w U) (c U) y
    have hm (r) (hr : r ∈ I) : Measurable (f r) :=
      ordinaryFineAliasRawAction_spatial_measurable _ _ _ _ _ hell (hell.trans (hLT r hr))
        M r q C a V eta p g w hpmeas hgmeas hwmeas c hcmeas y
    have hi (r) (hr : r ∈ I) := ordinaryFineAliasRawAction_spatial_square_integrable_and_le hd
      ad bd c0 _ (T r) haD hshrink htau (hI r hr).1 (hI r hr).2 hell (hell.trans (hLT r hr)) (hLT r hr)
      q hn C a V eta rho hC ha heta hrho hetarho p g w hpmeas hgmeas hwmeas c hcmeas hpD hg hw hc hp y
    have hb (r) (hr : r ∈ I) : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤ B :=
      (hi r hr).2.trans (ordinaryFineAliasSpatialBudget_source_scale_le hd (hI r hr).2 hbd hD hK hc0
        hDK hN hell hH q)
    exact (finite_sum_square_integral_le (fullSpatialPatchDesign d n) I f B hm
      (fun r hr => (hi r hr).1) hb).trans (mul_le_mul_of_nonneg_right hcard hB)
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin n → Fin 3))) => hsum y)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hs
  exact hs.trans_eq (by
    unfold B ordinaryAliasFamilySpatialPrefactor ordinaryAliasSpatialResponseBase
    rw [mul_pow]
    ring)


/-- Numerical guards for the actual canonical fine-alias scale. -/
structure OrdinaryFineAliasSaddleGuards (s : ℝ) (d : ℕ) (ad bd Cw x : ℝ) : Prop where
  dimension : 5 ≤ d
  shrunkInterval : ad+(lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)⁻¹ <
    bd-(lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)⁻¹
  exponent : shrunkDensityExponent ad bd
    (lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x) ≤ densityIntervalExponent ad bd+1
  degree : (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ) ≤
    (((d : ℝ)+8)/4+1)*(lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)
  cutoff : 1 ≤ lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
    (shrunkDensityExponent ad bd) x
  logarithm : Real.log (1+Real.log (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)) ≤
      lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x
  targets : ∀ r ∈ ordinaryFineAliasTargetSet d
    (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x)
    (lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
      (shrunkDensityExponent ad bd) x)
    (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)
    (lowerSaddleMu d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw x),
    2 ≤ r ∧ r ≤ lowerAliasFineTargetBound d
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) (densityIntervalExponent ad bd+1)

/-- All guards come from the canonical rounded saddle and actual shrunk
endpoints, with a fixed number of fine targets before count/spatial tuples. -/
theorem eventually_ordinaryFineAlias_saddle_guards {s ad bd : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4*s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd) (Cw : ℝ) :
    ∀ᶠ x in atTop, OrdinaryFineAliasSaddleGuards s d ad bd Cw x := by
  let tau := densityIntervalExponent ad bd
  let m := lowerSaddleCoefficient s d tau
  let theta := lowerSaddleTheta s d tau
  have htau : 0 < tau := densityIntervalExponent_pos haD hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hM := lowerSaddleM_tendsto_atTop hm
  have hsmall := hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : (0 : ℝ)<(bd-ad)/2))
  filter_upwards [actual_lowerAlias_hierarchy hs hd haD hab (Cact := 1) (Cs := 1)
      (by norm_num) (by norm_num) Cw,
    hM.eventually (eventually_ge_atTop (1 : ℝ)), hsmall] with x hh hM1 hsmall
  simp only [Pi.inv_apply] at hsmall
  rcases hh with ⟨hell,hτ,_hbase,hlog,_hgap,_hq21,_hq1,_hDq,_hco,_hsingle,_hRM,hactive⟩
  have hd0 : (0 : ℝ)<d := by linarith
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by exact_mod_cast h
    omega
  refine ⟨hd5, by change ad+(lowerSaddleM m x : ℝ)⁻¹<bd-(lowerSaddleM m x : ℝ)⁻¹; linarith,
    hτ, lowerSaddleD_le_fixed_linear hd0 hM1, hell.le, hlog, ?_⟩
  intro r hr
  have hrmem := (Finset.mem_filter.mp hr).2
  refine ⟨by omega, hactive r ?_⟩
  exact hrmem.2

/-- The final ordinary fine-alias estimate for the paper's actual rounded
saddle, uniformly at every count and every measurable nuisance tuple.
The fixed constants are selected before x,n,F and the nuisance fields. -/
theorem eventually_ordinaryFineAliasFamily_spatial_response_energy {s ad bd : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4*s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd)
    (Cw : ℝ) (q : ℕ) (C a rho : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hrho : 0 ≤ rho) :
    ∀ᶠ x in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent ad bd)
      let theta := lowerSaddleTheta s d (densityIntervalExponent ad bd)
      let c0 := densityIntervalExponent ad bd+1
      let M := lowerSaddleM m x
      let D := lowerSaddleD d m x
      let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
      let mu := lowerSaddleMu d m theta Cw x
      let L := lowerAliasCutoff s d m theta Cw c0 (shrunkDensityExponent ad bd) x
      let R := lowerAliasFineTargetBound d theta c0
      ∀ (n F : ℕ), 1 ≤ n → ∀ (V eta : ℝ), 0 ≤ eta → eta ≤ rho/2 →
      ∀ (p g w : (Fin n → Covariate d) → Fin n → ℝ)
        (c : (Fin n → Covariate d) → HighFrameIndex d F → ℝ),
      (∀ i, Measurable (fun U => p U i)) →
      (∀ i, Measurable (fun U => g U i)) →
      (∀ i, Measurable (fun U => w U i)) →
      (∀ gamma, Measurable (fun U => c U gamma)) →
      (∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, p U i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)) →
      (∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |g U i| ≤ rho/2) →
      (∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |w U i| ≤ 1) →
      (∀ᵐ U ∂fullSpatialPatchDesign d n, ∑ gamma, |c U gamma| ≤ C⁻¹) →
      (∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) →
      (∑ y : Fin n → Fin 3, ∫ U,
        ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D L N mu)
          (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d) L
          (fun r => higherBandTargetScale d r N mu) M q C a V eta U
          (p U) (g U) (w U) (c U) y^2 ∂fullSpatialPatchDesign d n) ≤
        ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho *
          eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
            Real.exp (lowerAliasSpatialFixedL d theta c0*M) * (ordinaryAliasSpatialResponseBase d bd)^n := by
  filter_upwards [eventually_ordinaryFineAlias_saddle_guards hs hd haD hab Cw] with x hx
  dsimp only
  intro n F hn V eta heta hetarho p g w c hpmeas hgmeas hwmeas hcmeas hpD hg hw hc hp
  have hc0 : 0 ≤ densityIntervalExponent ad bd+1 := by linarith [densityIntervalExponent_pos haD hab]
  have hLT : ∀ r ∈ ordinaryFineAliasTargetSet d
      (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x)
      (lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
        (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
        (shrunkDensityExponent ad bd) x)
      (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
        (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)
      (lowerSaddleMu d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
        (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw x),
    lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
        (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
        (shrunkDensityExponent ad bd) x ≤
      higherBandTargetScale d r
        (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
          (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)
        (lowerSaddleMu d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
          (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw x) :=
    fun r hr => (Finset.mem_filter.mp hr).2.2.le
  exact ordinaryFineAliasFamilyRawAction_spatial_response_energy_le hx.dimension _ ad bd _ _ _ _ _
    haD hx.shrunkInterval hx.exponent hx.targets (Nat.cast_nonneg _) (by positivity) hc0 hx.degree
    (lowerSaddleN_positive _ _ _ _ _ _ _) hx.cutoff hx.logarithm hLT q hn C a V eta rho hC ha
    heta hrho hetarho p g w hpmeas hgmeas hwmeas c hcmeas hpD hg hw hc hp

end NearlyMinimax
