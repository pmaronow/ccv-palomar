module

public import NearlyMinimax.CardinalProductDesign
public import NearlyMinimax.ExponentialSpatialKernels


@[expose] public section

/-! Exact finite-product marginalization and subset kernel lifting on Q^k. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem pi_finset_subtype_instance_eq {I E : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E) (s : Finset I) :
    (@Measure.pi s (fun _ => E) (Subtype.fintype (fun i => i ∈ s))
      (fun _ => inferInstance) (fun _ => μ)) = Measure.pi (fun _ : s => μ) := by
  congr 1
  exact Subsingleton.elim _ _

theorem finite_pi_subset_integral {I E : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (s : Finset I) (f : (s → E) → ℝ) :
    (∫ U : I → E, f (fun j : s => U j.val) ∂Measure.pi (fun _ : I => μ)) =
      μ.real univ ^ (Fintype.card I - s.card) * ∫ V, f V ∂Measure.pi (fun _ : s => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => E) (fun i => i ∈ s)
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => μ) (fun i => i ∈ s)
  rw [pi_finset_subtype_instance_eq μ s] at hp
  have he : (∫ U : I → E, f (fun j : s => U j.val) ∂Measure.pi (fun _ : I => μ)) =
      ∫ z : (s → E) × ({i : I // i ∉ s} → E), f z.1
        ∂(Measure.pi (fun _ : s => μ)).prod (Measure.pi (fun _ : {i : I // i ∉ s} => μ)) := by
    have h := hp.symm.integral_comp' (fun U : I → E => f (fun j : s => U j.val))
    have hf (z : (s → E) × ({i : I // i ∉ s} → E)) :
        (fun j : s => e.symm z j.val) = z.1 := by
      funext j
      change (if h : j.val ∈ s then z.1 ⟨j.val, h⟩ else z.2 ⟨j.val, h⟩) = z.1 j
      simp [j.property]
    change (∫ z : (s → E) × ({i : I // i ∉ s} → E), f (fun j : s => e.symm z j.val)
      ∂(Measure.pi (fun _ : s => μ)).prod (Measure.pi (fun _ : {i : I // i ∉ s} => μ))) = _ at h
    simp_rw [hf] at h
    exact h.symm
  rw [he, integral_fun_fst]
  have hc : (Measure.pi (fun _ : {i : I // i ∉ s} => μ)).real univ =
      μ.real univ ^ (Fintype.card I - s.card) := by
    simp only [measureReal_def, Measure.pi_univ, Finset.prod_const, Finset.card_univ,
      ENNReal.toReal_pow]
    rw [Fintype.card_subtype_compl]
    simp
  rw [hc]
  rfl

theorem finite_pi_subset_integrable {I E : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (s : Finset I) (f : (s → E) → ℝ) (hf : Integrable f (Measure.pi (fun _ : s => μ))) :
    Integrable (fun U : I → E => f (fun j : s => U j.val)) (Measure.pi (fun _ : I => μ)) := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => μ) (fun i => i ∈ s)
  rw [pi_finset_subtype_instance_eq μ s] at hp
  have hi : Integrable (fun z : (s → E) × ({i : I // i ∉ s} → E) => f z.1)
      ((Measure.pi (fun _ : s => μ)).prod (Measure.pi (fun _ : {i : I // i ∉ s} => μ))) :=
    hf.comp_fst _
  exact hp.integrable_comp_of_integrable hi

theorem spatial_subset_square_integral {d k : ℕ} (s : Finset (Fin k))
    (f : (s → Covariate d) → ℝ) :
    (∫ U : Fin k → Covariate d, f (fun j : s => U j.val) ^ 2 ∂fullSpatialPatchDesign d k) =
      (2 : ℝ) ^ (d * (k - s.card)) *
        ∫ V, f V ^ 2 ∂Measure.pi (fun _ : s => volume.restrict (spatialPatchBox d)) := by
  rw [fullSpatialPatchDesign, finite_pi_subset_integral
    (volume.restrict (spatialPatchBox d)) s (fun V => f V ^ 2)]
  simp only [measureReal_def, Measure.restrict_apply_univ, Fintype.card_fin]
  change (volume.real (spatialPatchBox d)) ^ (k - s.card) * _ = _
  rw [spatialPatchBox_real_volume, ← pow_mul]

def spatialSubsetConfiguration {d k : ℕ} (s : Finset (Fin k))
    (U : Fin k → Covariate d) : Fin s.card → Covariate d :=
  fun j => U ((Fintype.equivFin s).symm (Fin.cast (Fintype.card_coe s).symm j)).val

theorem spatialSubsetConfiguration_measurable {d k : ℕ} (s : Finset (Fin k)) :
    Measurable (spatialSubsetConfiguration (d := d) s) := by
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply _

theorem finite_pi_reindex_integral {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (e : I ≃ J) (f : (J → E) → ℝ) :
    (∫ U : I → E, f (fun j => U (e.symm j)) ∂Measure.pi (fun _ : I => μ)) =
      ∫ V, f V ∂Measure.pi (fun _ : J => μ) := by
  have h := (measurePreserving_piCongrLeft (fun _ : J => μ) e).integral_comp' f
  have he (U : I → E) : (Equiv.piCongrLeft (fun _ : J => E) e) U =
      fun j => U (e.symm j) := by
    funext j
    simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  simp only [MeasurableEquiv.coe_piCongrLeft] at h
  simp_rw [he] at h
  exact h

theorem spatial_subset_square_integral_enumerated {d k : ℕ} (s : Finset (Fin k))
    (f : (Fin s.card → Covariate d) → ℝ) :
    (∫ U : Fin k → Covariate d, f (spatialSubsetConfiguration s U) ^ 2
      ∂fullSpatialPatchDesign d k) = (2 : ℝ) ^ (d * (k - s.card)) *
        ∫ V, f V ^ 2 ∂fullSpatialPatchDesign d s.card := by
  let e : s ≃ Fin s.card := (Fintype.equivFin s).trans (finCongr (Fintype.card_coe s))
  have he (U : Fin k → Covariate d) : spatialSubsetConfiguration s U =
      fun j => (fun l : s => U l.val) (e.symm j) := by
    funext j
    rfl
  simp_rw [he]
  rw [spatial_subset_square_integral s (fun V => f (fun j => V (e.symm j)))]
  rw [finite_pi_reindex_integral (volume.restrict (spatialPatchBox d)) e (fun V => f V ^ 2)]
  rfl

end NearlyMinimax
