module

public import NearlyMinimax.CardinalInterpolationBias
public import NearlyMinimax.Risk


@[expose] public section

/-! Weighted Cauchy--Schwarz for actual cardinal scale measures. The
pointwise domination is squared to include all collision configurations. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

/-- A genuine integral inequality from pointwise squared domination;
no conclusion about an interpolation kernel is assumed. -/
theorem integral_square_le_weight_mass_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h w g : α → ℝ) (hh : Integrable h μ)
    (hw : Integrable w μ) (hg : Integrable g μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hdom : ∀ᵐ x ∂μ, (h x) ^ 2 ≤ w x * g x) :
    (∫ x, h x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, g x ∂μ) := by
  have hws : AEStronglyMeasurable (fun x => Real.sqrt (w x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hgs : AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hew : (fun x => Real.sqrt (w x) ^ 2) =ᵐ[μ] w := by
    filter_upwards [hwn] with x hx
    exact Real.sq_sqrt hx
  have heg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hgn] with x hx
    exact Real.sq_sqrt hx
  have hwL : MemLp (fun x => Real.sqrt (w x)) 2 μ :=
    (memLp_two_iff_integrable_sq hws).mpr (hw.congr hew.symm)
  have hgL : MemLp (fun x => Real.sqrt (g x)) 2 μ :=
    (memLp_two_iff_integrable_sq hgs).mpr (hg.congr heg.symm)
  have hprodL : MemLp (fun x => Real.sqrt (w x) * Real.sqrt (g x)) 1 μ := hwL.fun_mul hgL
  have hprod := memLp_one_iff_integrable.mp hprodL
  have hpoint : (fun x => |h x|) ≤ᵐ[μ] (fun x => Real.sqrt (w x) * Real.sqrt (g x)) := by
    filter_upwards [hwn, hgn, hdom] with x hx hy hz
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] using hz
  have hcs := integral_cauchy_schwarz μ _ _ hwL hgL
  rw [integral_congr_ae hew, integral_congr_ae heg] at hcs
  have hW : 0 ≤ ∫ x, w x ∂μ := integral_nonneg_of_ae hwn
  have hG : 0 ≤ ∫ x, g x ∂μ := integral_nonneg_of_ae hgn
  have hbound : |∫ x, h x ∂μ| ≤ Real.sqrt (∫ x, w x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
    calc
      _ ≤ ∫ x, |h x| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm h
      _ ≤ ∫ x, Real.sqrt (w x) * Real.sqrt (g x) ∂μ := integral_mono_ae hh.abs hprod hpoint
      _ ≤ |∫ x, Real.sqrt (w x) * Real.sqrt (g x) ∂μ| := le_abs_self _
      _ ≤ _ := hcs
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hbound
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hW, Real.sq_sqrt hG] using hs

/-- The actual Gamma-normalized cardinal weights have mass at most one
also after any measurable scale restriction. -/
theorem anchored_cardinal_weight_mass_restrict_le {d n : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d)
    (s : Set (SpatialScaleVector i)) (hs : s ⊆ Ici 0) :
    (∫ t in s, anchoredCardinalScaleWeight i lam x t Y) ≤ 1 := by
  apply (integral_mono_measure (Measure.restrict_mono_set volume hs)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [anchored_cardinal_scale_product]
      apply Finset.prod_nonneg
      intro j hj
      unfold spatialUnaryWeight
      exact mul_nonneg (mul_nonneg (ht j) (sq_nonneg _)) (Real.exp_pos _).le)
    (anchored_cardinal_scale_integrable i hlam x Y)).trans
  exact spatial_cardinal_weight_orthant_integral_le_one i lam hlam (anchoredPatchConfiguration i x Y)

end NearlyMinimax
