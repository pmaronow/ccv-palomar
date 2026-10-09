module

public import NearlyMinimax.OrdinaryFineAliasAggregation


@[expose] public section

/-! Deterministic response-summed square envelopes for ordinary fine aliases.
They depend only on actual geometric matrix kernels and fixed scalar data,
never on the density/regression/window/coefficient nuisance values. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def ordinaryFineAliasAmplitudeFactor (n M R q : ℕ) (ad bd c0 C a rho eta : ℝ) : ℝ :=
  ((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
    Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
      (ordinaryAliasResponseConstant q C a rho * (n : ℝ)^2 * eta^2)

def ordinaryFineAliasGeometryKernel {d n F : ℕ} (r : ℕ) (L T : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
      (spatialSubsetConfiguration S U))

/-- The actual universal envelope on the full Q^n spatial domain. -/
def ordinaryFineAliasResponseSquareEnvelope {d n F : ℕ} (M r R q : ℕ)
    (ad bd c0 C a rho eta L T : ℝ) (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n * (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)^2 *
    (ordinaryFineAliasGeometryKernel (F := F) r L T U)^2

/-- Sum the actual geometric bands before squaring. This is the genuine
triangle/Cauchy envelope for the sum of fine signed-row actions. -/
def ordinaryFineAliasFamilyResponseSquareEnvelope {d n F : ℕ} (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n *
    (∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r L (T r) U)^2

theorem ordinaryFineAliasGeometryKernel_nonneg {d n F : ℕ} (r : ℕ) (L T : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ ordinaryFineAliasGeometryKernel (F := F) r L T U :=
  Finset.sum_nonneg (fun _ _ => spatial_matrix_l1_nonnegative _)

theorem ordinaryFineAliasAmplitudeFactor_nonneg (n M R q : ℕ) {ad bd : ℝ}
    (haD : 0 < ad) (hab : ad < bd) (c0 C a rho eta : ℝ) :
    0 ≤ ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta := by
  have hbd : 0 < bd := haD.trans hab
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase ad bd c0 := by
    unfold uniformOrdinaryDensityActivityBase
    positivity
  have := ordinaryAliasResponseConstant_nonneg q C a rho
  unfold ordinaryFineAliasAmplitudeFactor
  positivity

theorem ordinaryFineAliasResponseSquareEnvelope_nonneg {d n F : ℕ} (M r R q : ℕ)
    (ad bd c0 C a rho eta L T : ℝ) (U : Fin n → Covariate d) :
    0 ≤ ordinaryFineAliasResponseSquareEnvelope (F := F) M r R q ad bd c0 C a rho eta L T U := by
  unfold ordinaryFineAliasResponseSquareEnvelope
  positivity

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg {d n F : ℕ} (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ) (U : Fin n → Covariate d) :
    0 ≤ ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  unfold ordinaryFineAliasFamilyResponseSquareEnvelope
  positivity

theorem ordinaryFineAliasGeometryKernel_measurable {d n F : ℕ} (r : ℕ) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 1 ≤ T) :
    Measurable (ordinaryFineAliasGeometryKernel (d := d) (n := n) (F := F) r L T) := by
  unfold ordinaryFineAliasGeometryKernel spatialMatrixL1
  exact Finset.measurable_sum _ (fun S _ => Finset.measurable_sum _
    (fun gamma _ => Finset.measurable_sum _ (fun beta _ =>
      ((integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT gamma beta).measurable.abs).comp
        (spatialSubsetConfiguration_measurable S))))

theorem ordinaryFineAliasResponseSquareEnvelope_measurable {d n F : ℕ} (M r R q : ℕ)
    (ad bd c0 C a rho eta : ℝ) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) :
    Measurable (ordinaryFineAliasResponseSquareEnvelope (d := d) (n := n) (F := F)
      M r R q ad bd c0 C a rho eta L T) :=
  ((ordinaryFineAliasGeometryKernel_measurable r hL hT).pow_const 2).const_mul _

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_measurable {d n F : ℕ}
    (I : Finset ℕ) (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ)
    (hL : 1 ≤ L) (hT : ∀ r ∈ I, 1 ≤ T r) :
    Measurable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a rho eta L T) :=
  ((Finset.measurable_sum I (fun r hr =>
    (ordinaryFineAliasGeometryKernel_measurable r hL (hT r hr)).const_mul _)).pow_const 2).const_mul _

/-- Honest pointwise domination, separately uniform over every response's
nuisance values. No measurability or constructed inverse chart for the
nuisances is required to bound their supremum. -/
theorem ordinaryFineAliasResponseSquareEnvelope_dominates {d n F M r R : ℕ}
    (ad bd c0 L T : ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) (C a V eta rho : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho) (hetarho : eta ≤ rho/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : (Fin n → Fin 3) → Fin n → ℝ)
    (c : (Fin n → Fin 3) → HighFrameIndex d F → ℝ)
    (hpD : ∀ y i, p y i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ y i, |g y i| ≤ rho/2) (hw : ∀ y i, |w y i| ≤ 1)
    (hc : ∀ y, ∑ gamma, |c y gamma| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3,
      ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
        L T M r q C a V eta U (p y) (g y) (w y) (c y) y^2) ≤
      ordinaryFineAliasResponseSquareEnvelope (F := F) M r R q ad bd c0 C a rho eta L T U := by
  let K := ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta
  let H := ordinaryFineAliasGeometryKernel (F := F) r L T U
  have hb (y : Fin n → Fin 3) :
      ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
        L T M r q C a V eta U (p y) (g y) (w y) (c y) y^2 ≤ K^2*H^2 := by
    have h := ordinaryFineAliasRawAction_abs_bound_of_chart ad bd c0 (spatialInterpolationLambda d) L T haD hshrink htau hr hrR
      q hn C a V eta rho hC ha heta hrho hetarho U hU (p y) (g y) (w y) (hpD y) (hg y) (hw y)
      (c y) (hc y) hp y
    change |ordinaryFineAliasRawAction _ _ _ L T M r q C a V eta U (p y) (g y) (w y) (c y) y| ≤ K*H at h
    simpa only [sq_abs, mul_pow] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin n → Fin 3))) => hb y)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ordinaryFineAliasResponseSquareEnvelope, K, H, mul_assoc] using hs

/-- Genuine Q^n square-kernel integration gives the exact response-count
factor. Desired envelope integrability or moments are not premises. -/
theorem ordinaryFineAliasResponseSquareEnvelope_integrable_and_le {d n F M r R : ℕ}
    (hd : 5 ≤ d) (hr : 2 ≤ r) (ad bd c0 C a rho eta : ℝ)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) (q : ℕ) :
    Integrable (ordinaryFineAliasResponseSquareEnvelope (d := d) (n := n) (F := F)
      M r R q ad bd c0 C a rho eta L T) (fullSpatialPatchDesign d n) ∧
    (∫ U, ordinaryFineAliasResponseSquareEnvelope (F := F) M r R q ad bd c0 C a rho eta L T U
      ∂fullSpatialPatchDesign d n) ≤
        (3 : ℝ)^n*ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a rho eta L := by
  have h := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n) hd hr hL hT hLT
  let K := ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta
  have hi := h.1.const_mul ((3 : ℝ)^n*K^2)
  refine ⟨hi, ?_⟩
  rw [show (∫ U, ordinaryFineAliasResponseSquareEnvelope (F := F) M r R q ad bd c0 C a rho eta L T U
      ∂fullSpatialPatchDesign d n) =
    ((3 : ℝ)^n*K^2)*(∫ U, (ordinaryFineAliasGeometryKernel (F := F) r L T U)^2
      ∂fullSpatialPatchDesign d n) by rw [← integral_const_mul]; rfl]
  exact (mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (3 : ℝ)^n*K^2)).trans_eq (by
    unfold ordinaryFineAliasSpatialBudget K ordinaryFineAliasAmplitudeFactor
    ring)


/-- Actual pointwise square domination for the entire fine family,
separately uniform over each response's nuisance tuple. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_dominates {d n F M R : ℕ}
    (I : Finset ℕ) (ad bd c0 L : ℝ) (T : ℕ → ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hI : ∀ r ∈ I, 1 ≤ r ∧ r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) (C a V eta rho : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho) (hetarho : eta ≤ rho/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : (Fin n → Fin 3) → Fin n → ℝ)
    (c : (Fin n → Fin 3) → HighFrameIndex d F → ℝ)
    (hpD : ∀ y i, p y i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ y i, |g y i| ≤ rho/2) (hw : ∀ y i, |w y i| ≤ 1)
    (hc : ∀ y, ∑ gamma, |c y gamma| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3,
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
        L T M q C a V eta U (p y) (g y) (w y) (c y) y^2) ≤
      ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  let H := ∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hb (y : Fin n → Fin 3) :
      |ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y| ≤ H := by
    apply (Finset.abs_sum_le_sum_abs _ I).trans
    exact Finset.sum_le_sum (fun r hr =>
      ordinaryFineAliasRawAction_abs_bound_of_chart ad bd c0 (spatialInterpolationLambda d) L (T r)
        haD hshrink htau (hI r hr).1 (hI r hr).2 q hn C a V eta rho hC ha heta hrho hetarho
        U hU (p y) (g y) (w y) (hpD y) (hg y) (hw y) (c y) (hc y) hp y)
  have hsq (y : Fin n → Fin 3) :
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y^2 ≤ H^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hb y))).mpr (hb y)
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin n → Fin 3))) => hsq y)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ordinaryFineAliasFamilyResponseSquareEnvelope, H] using hs

/-- True integrability and geometric scale for the response-summed family
envelope itself; independent of every nuisance field and chart inverse. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le {d n F M R : ℕ}
    (hd : 5 ≤ d) (I : Finset ℕ) (hI : ∀ r ∈ I, 2 ≤ r ∧ r ≤ R)
    (ad bd c0 C a rho eta D K N : ℝ) (hbd : 0 ≤ bd)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M)
    (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) (T : ℕ → ℝ)
    (hLT : ∀ r ∈ I, N*Real.exp (-c0*D) ≤ T r) (q : ℕ) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T) (fullSpatialPatchDesign d n) ∧
    (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T U ∂fullSpatialPatchDesign d n) ≤
      ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho *
        eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialResponseBase d bd)^n := by
  let f := fun r (U : Fin n → Covariate d) =>
    ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r (N*Real.exp (-c0*D)) (T r) U
  let B := ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho *
    eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
      Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have := ordinaryAliasSpatialPrefactor_nonneg d q R ad bd c0 C a rho
    unfold ordinaryAliasSpatialCountBase
    positivity
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hell (hell.trans (hLT r hr))).const_mul _
  have hk (r) (hr : r ∈ I) := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
    hd (hI r hr).1 hell (hell.trans (hLT r hr)) (hLT r hr)
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U^2) (fullSpatialPatchDesign d n) := by
    have h := (hk r hr).1.const_mul ((ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)^2)
    convert h using 1
    funext U
    dsimp [f, ordinaryFineAliasGeometryKernel]
    ring
  have hb (r) (hr : r ∈ I) : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤ B := by
    have h : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤
        ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) := by
      have hid : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) =
          (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)^2 *
            (∫ U, (ordinaryFineAliasGeometryKernel (F := F) r (N*Real.exp (-c0*D)) (T r) U)^2
              ∂fullSpatialPatchDesign d n) := by
        rw [← integral_const_mul]
        congr 1
        funext U
        dsimp [f]
        ring
      rw [hid]
      exact (mul_le_mul_of_nonneg_left (hk r hr).2 (sq_nonneg _)).trans_eq (by
        unfold ordinaryFineAliasSpatialBudget ordinaryFineAliasAmplitudeFactor
        ring)
    exact h.trans (ordinaryFineAliasSpatialBudget_source_scale_le hd (hI r hr).2 hbd hD hK hc0
      hDK hN hell hH q)
  have hs : Integrable (fun U => (∑ r ∈ I, f r U)^2) (fullSpatialPatchDesign d n) := by
    have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) I f hm hi
    have hupper : ∀ U, (∑ r ∈ I, f r U)^2 ≤ (∑ r ∈ I, |f r U|)^2 := by
      intro U
      have hb := Finset.abs_sum_le_sum_abs (fun r => f r U) I
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
        (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr hb
    exact h.mono' ((Finset.measurable_sum I hm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => by simpa only [Real.norm_eq_abs, abs_sq] using hupper U))
  have hcard : (I.card : ℝ)^2 ≤ ((R+1 : ℕ) : ℝ)^2 := by
    have hsub : I ⊆ Finset.range (R+1) := fun r hr => Finset.mem_range.mpr (by have := (hI r hr).2; omega)
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact_mod_cast Nat.pow_le_pow_left h 2
  have hsum := (finite_sum_square_integral_le (fullSpatialPatchDesign d n) I f B hm hi hb).trans
    (mul_le_mul_of_nonneg_right hcard hB)
  refine ⟨hs.const_mul ((3 : ℝ)^n), ?_⟩
  rw [show (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T U ∂fullSpatialPatchDesign d n) =
      (3 : ℝ)^n * (∫ U, (∑ r ∈ I, f r U)^2 ∂fullSpatialPatchDesign d n) by
    rw [← integral_const_mul]; rfl]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (3 : ℝ)^n)).trans_eq (by
    unfold B ordinaryAliasFamilySpatialPrefactor ordinaryAliasSpatialResponseBase
    rw [mul_pow]
    ring)

end NearlyMinimax
