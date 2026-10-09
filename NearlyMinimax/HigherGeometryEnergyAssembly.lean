module

public import NearlyMinimax.SpatialGeometryFactorialEnergy
public import NearlyMinimax.OrdinaryFineAliasSaddleEnvelope


@[expose] public section

/-! Actual higher-count envelope integration and factorial assembly. The
only intermediate ordinary-family input is its genuine finite spatial
integral sum; the canonical module derives it from the constructed bands. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem completeSourceHigherGeometryEnvelope_integral_eq {d r D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hr : 2 ≤ r) (aD bD c0 ell N mu : ℝ) (M R q : ℕ)
    (C a rho eta : ℝ) (hell : 1 ≤ ell) (hellN : ell ≤ N) :
    (∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := r) (D := D)
      aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d r) =
      4*((∫ U, cardinalGeometryEnvelope (d := d) (n := r) (F := D) q (bD-(M : ℝ)⁻¹) C a rho eta
          (max 1 (higherBandTargetScale d r N mu)) U ∂fullSpatialPatchDesign d r) +
        (if M<r then ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
          (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
          (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d r else 0) +
        (if M<r then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := r)
          (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d r else 0) +
        (∫ U, fineFieldGeometryEnvelope (d := d) (n := r)
          (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d r)) := by
  have hA := (cardinalGeometryEnvelope_integrable_and_le (d := d) (n := r) (F := D) hd hr q
    (bD-(M : ℝ)⁻¹) C a rho eta (T := max 1 (higherBandTargetScale d r N mu)) (le_max_left _ _)).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (d := d) (n := r) (F := D) hd
    (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
    (fun t => higherBandTargetScale d t N mu) hell (fun t ht => by
      have h := (Finset.mem_filter.mp ht).2
      exact ⟨by omega,h.2.le⟩)
  have hP := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := r) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N (lt_of_lt_of_le zero_lt_one hell) hellN M q C a rho eta).1
  have hF := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := r) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N (lt_of_lt_of_le zero_lt_one hell) M q C a rho eta).1
  unfold completeSourceHigherGeometryEnvelope
  by_cases hMr : M<r
  · simp only [if_pos hMr]
    rw [integral_const_mul]
    have h1 := integral_add ((hA.add hB).add hP) hF
    have h2 := integral_add (hA.add hB) hP
    have h3 := integral_add hA hB
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1,h2,h3]
  · simp only [if_neg hMr,add_zero]
    rw [integral_const_mul,integral_add hA hF]

theorem finite_complete_higher_geometry_energy_le {d D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hD : 3 ≤ D) (aD bD c0 K ell N mu : ℝ) (M R q : ℕ)
    (C a rho eta Cs Eord : ℝ) (haD : 0 < aD) (ha : 0 < a)
    (hshrink : aD+(M : ℝ)⁻¹ < bD-(M : ℝ)⁻¹)
    (htau : exteriorTau (((aD+(M : ℝ)⁻¹)+(bD-(M : ℝ)⁻¹))/
      ((bD-(M : ℝ)⁻¹)-(aD+(M : ℝ)⁻¹))) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (hCs : 0 ≤ Cs)
    (hell : 1 ≤ ell) (hellN : ell ≤ N) (hcut : ell=N*Real.exp (-c0*D))
    (hDM : (D : ℝ) ≤ K*M) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hmuH : mu*(1+Real.log N) ≤ 1) (hTaylor : eta^(4*q)*N^d ≤ 1)
    (hfield : Real.exp (2*exteriorTau (((aD+(M : ℝ)⁻¹)+(bD-(M : ℝ)⁻¹))/
        ((bD-(M : ℝ)⁻¹)-(aD+(M : ℝ)⁻¹)))*M) * (ell^(2-(d : ℝ)))^2 * mu^4 ≤
        mu^2*N^(-(d : ℝ)))
    (hord : (∑ j ∈ Finset.range (D-M), poissonCountWeight (Cs*mu) (M+1+j) *
      ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := M+1+j) (F := D)
        (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
        (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (M+1+j)) ≤ Eord) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3+j)) ≤
      4*(cardinalGeometryFactorialConstant d q bD C a rho Cs*eta^4*N^(-(d : ℝ))*mu^2 + Eord +
        finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs) *
          (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)*mu) (M+1) +
        finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ))) := by
  have hN : 1 ≤ N := hell.trans hellN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have had : aD ≤ aD+(M : ℝ)⁻¹ := le_add_of_nonneg_right
    (inv_nonneg.mpr (Nat.cast_nonneg M))
  have hbd : bD-(M : ℝ)⁻¹ ≤ bD := by linarith [inv_nonneg.mpr (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hbd0 : 0 ≤ bD-(M : ℝ)⁻¹ := (haD.trans_le had).le.trans hshrink.le
  have hA := finite_cardinal_geometry_budget_le (D := D) (F := D) hd hbd0 hbd q C a rho eta Cs ha hCs hN hmu hmu1 hmuH hTaylor
  have hP := finite_fine_pair_alias_geometry_budget_le (D := D) hd haD had hbd hshrink htau hc0 hK M q
    C a rho eta ell N Cs mu hNpos hcut hell hellN hDM hCs hmu.le hmu1
  have hF := finite_fine_field_geometry_budget_le (D := D) hd hD haD had hbd hshrink htau M q C a rho eta
    ell N Cs mu (lt_of_lt_of_le zero_lt_one hell) hCs hmu.le hmu1
  have hFconst : 0 ≤ finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs) := by
    unfold finePairFieldFactorialConstant fieldTailConstant
    have hPre := finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0
    have hP4 := poissonCountWeight_nonneg (by positivity [finePairFieldGeometricBase_nonneg d bD] :
      0 ≤ (3*Cs)*(finePairFieldGeometricBase d bD*2^12)) 4
    positivity
  have hFs := mul_le_mul_of_nonneg_left hfield
    (mul_nonneg hFconst (by positivity : 0 ≤ eta^4))
  have hFfinal : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3+j)
        (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j)) ≤
      finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ)) :=
    hF.trans (by convert hFs using 1 <;> ring)
  let f := fun r => poissonCountWeight (Cs*mu) r *
    ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := r) (F := D)
      (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
      (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d r
  have hf (r : ℕ) : 0 ≤ f r := mul_nonneg (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) r)
    (integral_nonneg (fun U => ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ U))
  have hO := (finite_refined_gated_sum_le_tail D M f hf).trans hord
  have heq : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3+j)) =
      4*((∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
        ∫ U, cardinalGeometryEnvelope (d := d) (n := 3+j) (F := D) q (bD-(M : ℝ)⁻¹) C a rho eta
          (max 1 (higherBandTargetScale d (3+j) N mu)) U ∂fullSpatialPatchDesign d (3+j)) +
        (∑ j ∈ Finset.range (D-2), if M<3+j then f (3+j) else 0) +
        (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
          (if M<3+j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3+j)
            (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j) else 0)) +
        (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
          ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3+j)
            (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j))) := by
    have hInt (j : ℕ) := completeSourceHigherGeometryEnvelope_integral_eq (d := d) (r := 3+j) (D := D)
      hd (by omega) aD bD c0 ell N mu M R q C a rho eta hell hellN
    simp_rw [hInt]
    try dsimp [f]
    have halg (w A B P F : ℝ) : w*(4*(A+B+P+F))=4*(w*A+w*B+w*P+w*F) := by ring
    simp_rw [halg,mul_ite,mul_zero]
    rw [←Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hO) hP) hFfinal) (by norm_num)

end NearlyMinimax
