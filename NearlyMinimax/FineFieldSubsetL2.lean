module

public import NearlyMinimax.FineFieldTimeL2


@[expose] public section

/-! Exact subset reindexing and genuine full-design energies of fine-field
moments, including all unused spatial coordinates. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem spatial_subset_product_reindex {d k : ℕ} (S : Finset (Fin k))
    (U : Fin k → Covariate d) (f : Covariate d → ℝ) :
    (∏ i ∈ S, f (U i)) = ∏ j : Fin S.card, f (spatialSubsetConfiguration S U j) := by
  classical
  let e : S ≃ Fin S.card := (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))
  rw [← Finset.prod_coe_sort S (fun i => f (U i))]
  exact (e.symm.prod_comp (fun i : S => f (U i.val))).symm

theorem finePairTimeSubsetMoment_reindex {d k : ℕ} (lo hi : ℝ)
    (U : Fin k → Covariate d) (S : Finset (Fin k)) :
    finePairTimeSubsetMoment lo hi U S =
      finePairTimeSubsetMoment lo hi (spatialSubsetConfiguration S U) Finset.univ := by
  unfold finePairTimeSubsetMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun e => by
    change e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i)) =
      e.1 * (∏ j : Fin S.card, finePairTimeFieldValue e (spatialSubsetConfiguration S U j))
    rw [spatial_subset_product_reindex S U (finePairTimeFieldValue e)])

theorem finePairTimeSubsetMoment_univ_measurable {d j : ℕ} [NeZero d] (lo hi : ℝ) :
    Measurable (fun U : Fin j → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ) := by
  have hm : Measurable (fun z : ℝ × (Fin j → Covariate d) =>
      z.1 * boundedHyperplaneSpatialMoment d z.1 j z.2) :=
    measurable_fst.mul (boundedHyperplaneSpatialMoment_joint_measurable d j)
  have h : Measurable (fun U : Fin j → Covariate d =>
      ∫ T in Icc lo hi, T * boundedHyperplaneSpatialMoment d T j U) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact h

theorem finePairTimeSubsetMoment_measurable {d k : ℕ} [NeZero d] (lo hi : ℝ)
    (S : Finset (Fin k)) :
    Measurable (fun U : Fin k → Covariate d => finePairTimeSubsetMoment lo hi U S) := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact (finePairTimeSubsetMoment_univ_measurable lo hi).comp (spatialSubsetConfiguration_measurable S)

theorem finePairTimeSubsetMoment_square_integrable {d k : ℕ} [NeZero d]
    (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
    Integrable (fun U : Fin k → Covariate d => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d k) := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integrable_enumerated S
    (fun V => finePairTimeSubsetMoment lo hi V Finset.univ)
    (finePairTimeSubsetMoment_univ_square_integrable hd hS hlo)

theorem finePairTimeSubsetMoment_square_integral_reindex {d k : ℕ}
    (lo hi : ℝ) (S : Finset (Fin k)) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) = (2 : ℝ) ^ (d * (k - S.card)) *
        ∫ V : Fin S.card → Covariate d, finePairTimeSubsetMoment lo hi V Finset.univ ^ 2
          ∂fullSpatialPatchDesign d S.card := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integral_enumerated (d := d) S
    (fun V => finePairTimeSubsetMoment lo hi V Finset.univ)

theorem finePairTimeSubsetMoment_square_integral_le {d k : ℕ} [NeZero d]
    (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      (2 : ℝ) ^ (d * (k - S.card)) *
        (hyperplaneSpatialMomentConstant d ^ S.card * (S.card : ℝ) ^ 4 * lo ^ (2 - (d : ℝ))) ^ 2 := by
  rw [finePairTimeSubsetMoment_square_integral_reindex]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb := finePairTimeSubsetMoment_univ_L2_le (d := d) hd hS (hi := hi) hlo
  have hn : 0 ≤ ∫ V : Fin S.card → Covariate d,
      finePairTimeSubsetMoment lo hi V Finset.univ ^ 2 ∂fullSpatialPatchDesign d S.card :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity [hyperplaneSpatialMomentConstant_positive d])).mpr hb
  simpa only [Real.sq_sqrt hn] using hs

end NearlyMinimax
