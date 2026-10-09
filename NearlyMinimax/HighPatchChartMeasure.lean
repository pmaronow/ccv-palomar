module

public import NearlyMinimax.HighLocalFrame
public import NearlyMinimax.SpatialPairProductIntegration


@[expose] public section

/-! Genuine pushforward control for torus patches and their affine local charts.
The bound includes a harmless factor 2^d for wrapping patches. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

def highAffineChart (d k : ℕ) (z : Fin d → ℤ) (x : Covariate d) : Covariate d :=
  fun r => (k : ℝ) * x r - z r

theorem highAffineChart_measurable (d k : ℕ) (z : Fin d → ℤ) :
    Measurable (highAffineChart d k z) := by unfold highAffineChart; fun_prop

theorem highAffineChart_map_volume (d k : ℕ) (hk : 0 < k) (z : Fin d → ℤ) :
    Measure.map (highAffineChart d k z) volume =
      ENNReal.ofReal ((k : ℝ)^d)⁻¹ • (volume : Measure (Covariate d)) := by
  let f : Covariate d →ₗ[ℝ] Covariate d := (k : ℝ) • LinearMap.id
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdet : LinearMap.det f = (k : ℝ)^d := by
    simp [f, LinearMap.det_smul, LinearMap.det_id]
  have hf := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f)
    (by rw [hdet]; positivity)
  have heq : highAffineChart d k z = (fun x : Covariate d => (fun r => -(z r : ℝ)) + x) ∘ f := by
    funext x r
    simp [highAffineChart, f]
    ring
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), hf, hdet,
    Measure.map_smul _ (by fun_prop), map_add_left_eq_self]
  congr 1
  rw [abs_of_nonneg (by positivity)]

theorem highPatch_lift_cube_cases (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (z : ℤ)
    (hz : (z : ZMod k) = j) (hclose : |(k : ℝ)*x-z| < 1) :
    z = (j.val : ℤ) ∨ z = (j.val : ℤ)+(k : ℤ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkv : (j.val : ℤ) < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ (k : ℤ) := by
    have hh := abs_lt.mp hclose
    have hzL : (-1 : ℝ) < z := by nlinarith [mul_nonneg hkR.le hx.1]
    have hzU : (z : ℝ) < k+1 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
    have hzLZ : (-1 : ℤ) < z := by exact_mod_cast hzL
    have hzUZ : z < (k : ℤ)+1 := by exact_mod_cast hzU
    omega
  have hqcases : q = 0 ∨ q = 1 := by
    have hj0 : (0 : ℤ) ≤ j.val := Int.natCast_nonneg _
    have hkZ : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
    have hqL : 0 ≤ q := by
      by_contra h
      have hqneg : q ≤ -1 := by omega
      nlinarith
    have hqU : q ≤ 1 := by
      by_contra h
      have hqbig : 2 ≤ q := by omega
      nlinarith
    omega
  rcases hqcases with hq0 | hq1
  · exact Or.inl (by simpa [hq0] using hq)
  · exact Or.inr (by simpa [hq1] using hq)

def highPatchWrapLift {d k : ℕ} (j : HighWindowLabels d k) (b : Fin d → Bool) : Fin d → ℤ :=
  fun r => if b r then (j r).val+(k : ℤ) else (j r).val

theorem highLocalCoordinates_eq_affine_on_patch {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) {x : Covariate d} (hx : x ∈ highTorusPatch d k j)
    (z : Fin d → ℤ) (hz : ∀ r, (z r : ZMod k)=j r)
    (hc : ∀ r, |(k : ℝ)*x r-z r| < 1) :
    highLocalCoordinates d k j x = highAffineChart d k z x := by
  funext r
  have he := highChartLift_eq_of_close k hk (j r) (x r) (z r) (hz r) (hc r)
  simp only [highLocalCoordinates, highLocalCoordinate, highRawChartCoordinate, he,
    if_pos (hc r).le, highAffineChart]

theorem highLocalCoordinates_patch_mem_box {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) {x : Covariate d} (hx : x ∈ highTorusPatch d k j) :
    highLocalCoordinates d k j x ∈ spatialPatchBox d := by
  obtain ⟨z, hz, hc⟩ := hx
  rw [highLocalCoordinates_eq_affine_on_patch hk j ⟨z,hz,hc⟩ z hz hc]
  change (∀ r, -1 ≤ highAffineChart d k z x r) ∧ (∀ r, highAffineChart d k z x r ≤ 1)
  constructor <;> intro r
  · exact (abs_lt.mp (hc r)).1.le
  · exact (abs_lt.mp (hc r)).2.le


/-- The genuine local-coordinate pushforward on a torus patch is dominated
by the scaled Lebesgue measure on [-1,1]^d.  The factor 2^d counts wrapping
chart lifts and is independent of the polynomial and all sample sizes. -/
theorem highLocalCoordinates_patch_map_le {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) :
    Measure.map (highLocalCoordinates d k j)
      ((cubeVolume d).restrict (highTorusPatch d k j)) ≤
      ENNReal.ofReal ((2 / (k : ℝ))^d) • volume.restrict (spatialPatchBox d) := by
  have hbox : MeasurableSet (spatialPatchBox d) := measurableSet_Icc
  apply Measure.le_iff.mpr
  intro S hS
  have hcover : (highLocalCoordinates d k j ⁻¹' S ∩ highTorusPatch d k j) ∩ unitCube d ⊆
      ⋃ b : Fin d → Bool, highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d) := by
    intro x hx
    obtain ⟨z, hz, hc⟩ := hx.1.2
    have hzcase (r : Fin d) : ∃ b : Bool,
        z r = if b then ((j r).val : ℤ)+(k : ℤ) else ((j r).val : ℤ) := by
      rcases highPatch_lift_cube_cases k hk (j r) (x r) (hx.2 r) (z r) (hz r) (hc r) with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    choose b hb using hzcase
    have hzb : z = highPatchWrapLift j b := by funext r; exact hb r
    have he := highLocalCoordinates_eq_affine_on_patch hk j hx.1.2 z hz hc
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    change highAffineChart d k (highPatchWrapLift j b) x ∈ S ∩ spatialPatchBox d
    rw [← hzb, ← he]
    exact ⟨hx.1.1, highLocalCoordinates_patch_mem_box hk j hx.1.2⟩
  rw [Measure.map_apply (highLocalCoordinates_measurable d k j) hS,
    Measure.restrict_apply ((highLocalCoordinates_measurable d k j) hS),
    cubeVolume, Measure.restrict_apply (((highLocalCoordinates_measurable d k j) hS).inter
      (highTorusPatch_measurableSet d k j)), Measure.smul_apply,
    Measure.restrict_apply hS, smul_eq_mul]
  calc
    _ ≤ volume (⋃ b : Fin d → Bool,
        highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d)) := measure_mono hcover
    _ ≤ ∑' b : Fin d → Bool,
        volume (highAffineChart d k (highPatchWrapLift j b) ⁻¹' (S ∩ spatialPatchBox d)) :=
      measure_iUnion_le _
    _ = ∑ b : Fin d → Bool,
        ENNReal.ofReal (((k : ℝ)^d)⁻¹) * volume (S ∩ spatialPatchBox d) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Measure.map_apply (highAffineChart_measurable d k _) (hS.inter hbox),
        highAffineChart_map_volume d k (by omega) _, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal ((2 / (k : ℝ))^d) * volume (S ∩ spatialPatchBox d) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc]
      congr 1
      have ht : (2 : ℝ≥0∞)^d = ENNReal.ofReal ((2 : ℝ)^d) := by
        rw [ENNReal.ofReal_pow] <;> norm_num
      rw [ht, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_pow]
      ring


/-- Lebesgue-integrable spatial functions remain integrable after evaluation
in the genuine torus patch chart. -/
theorem highLocalCoordinates_patch_integrable {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (H : Covariate d → ℝ)
    (hH : Integrable H (volume.restrict (spatialPatchBox d))) :
    Integrable (fun x => H (highLocalCoordinates d k j x))
      ((cubeVolume d).restrict (highTorusPatch d k j)) := by
  have hm : Integrable H (Measure.map (highLocalCoordinates d k j)
      ((cubeVolume d).restrict (highTorusPatch d k j))) :=
    (hH.smul_measure ENNReal.ofReal_ne_top).mono_measure
      (highLocalCoordinates_patch_map_le hk j)
  exact hm.comp_measurable (highLocalCoordinates_measurable d k j)

/-- True nonnegative integral comparison after the periodic chart map. -/
theorem highLocalCoordinates_patch_lintegral_le {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (H : Covariate d → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x, H (highLocalCoordinates d k j x)
      ∂(cubeVolume d).restrict (highTorusPatch d k j)) ≤
      ENNReal.ofReal ((2/(k : ℝ))^d) *
        ∫⁻ u, H u ∂volume.restrict (spatialPatchBox d) := by
  rw [← lintegral_map hH (highLocalCoordinates_measurable d k j)]
  exact (lintegral_mono' (highLocalCoordinates_patch_map_le hk j) le_rfl).trans_eq
    (lintegral_smul_measure _ _)

end NearlyMinimax
