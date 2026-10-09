module

public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.DyadicPilotFeatures


@[expose] public section

/-! Exact changes of variables for the actual regular-grid cells. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
namespace NearlyMinimax

def gridAffine {d : ℕ} (k : ℕ) (c : Fin d → Fin k) (w : Covariate d) : Covariate d :=
  regularGridCorner k c + (k : ℝ)⁻¹ • w

def gridClosedBox {d : ℕ} (k : ℕ) (c : Fin d → Fin k) : Set (Covariate d) :=
  Icc (regularGridCorner k c) (regularGridCorner k c + fun _ => (k : ℝ)⁻¹)

def gridAffineEquiv {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    Covariate d ≃ᵐ Covariate d :=
  ((Homeomorph.smul (Units.mk0 ((k : ℝ)⁻¹) (by positivity))).trans
    (Homeomorph.addLeft (regularGridCorner k c))).toMeasurableEquiv

@[simp] theorem gridAffineEquiv_apply {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) (w : Covariate d) : gridAffineEquiv k hk c w = gridAffine k c w := rfl

theorem gridAffine_preimage_box {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    gridAffine k c ⁻¹' gridClosedBox k c = unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  ext w
  change ((∀ i, regularGridCorner k c i ≤ regularGridCorner k c i + (k : ℝ)⁻¹ * w i) ∧
    (∀ i, regularGridCorner k c i + (k : ℝ)⁻¹ * w i ≤ regularGridCorner k c i + (k : ℝ)⁻¹)) ↔
    ∀ i, 0 ≤ w i ∧ w i ≤ 1
  constructor
  · intro hw i
    constructor
    · exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hkr)).mp (by linarith [hw.1 i])
    · apply (mul_le_mul_iff_of_pos_left (inv_pos.mpr hkr)).mp
      simpa using (show (k : ℝ)⁻¹ * w i ≤ (k : ℝ)⁻¹ by linarith [hw.2 i])
  · intro hw
    constructor <;> intro i
    · linarith [mul_nonneg (inv_nonneg.mpr hkr.le) (hw i).1]
    · have := mul_le_mul_of_nonneg_left (hw i).2 (inv_nonneg.mpr hkr.le)
      linarith

theorem gridClosedBox_subset_cube {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) : gridClosedBox k c ⊆ unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  intro z hz i
  refine ⟨(regular_grid_corner_mem_cube k hk c i).1.trans (hz.1 i), ?_⟩
  apply (hz.2 i).trans
  change (c i : ℝ) / k + (k : ℝ)⁻¹ ≤ 1
  have hc : ((c i).val : ℝ) + 1 ≤ k := by exact_mod_cast (c i).isLt
  have he : (c i : ℝ) / k + (k : ℝ)⁻¹ = ((c i : ℝ) + 1) / k := by ring
  rw [he]
  exact (div_le_one hkr).2 hc

theorem gridAffine_map_volume {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    (volume : Measure (Covariate d)).map (gridAffine k c) =
      ENNReal.ofReal ((k : ℝ) ^ d) • volume := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [show gridAffine k c = (fun z => regularGridCorner k c + z) ∘
    (fun w => (k : ℝ)⁻¹ • w) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume (inv_ne_zero hkr.ne'),
    Measure.map_smul _ (by fun_prop), map_add_left_eq_self]
  simp [Module.finrank_pi, abs_of_nonneg (pow_nonneg hkr.le d)]

/-- The Jacobian is the exact number of regular-grid cells. -/
theorem gridAffine_map_cubeVolume {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    (cubeVolume d).map (gridAffine k c) =
      ENNReal.ofReal ((k : ℝ) ^ d) • volume.restrict (gridClosedBox k c) := by
  let e := gridAffineEquiv k hk c
  have hpre : e ⁻¹' gridClosedBox k c = unitCube d := gridAffine_preimage_box k hk c
  have h := e.restrict_map (volume : Measure (Covariate d)) (gridClosedBox k c)
  rw [hpre] at h
  change ((volume.restrict (unitCube d)).map e) = _
  rw [← h]
  change ((volume : Measure (Covariate d)).map (gridAffine k c)).restrict _ = _
  rw [gridAffine_map_volume k hk c, Measure.restrict_smul]

theorem gridAffine_integral {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k)
    (f : Covariate d → ℝ) :
    (∫ w, f (gridAffine k c w) ∂cubeVolume d) =
      (k : ℝ) ^ d * ∫ z in gridClosedBox k c, f z := by
  have h := integral_map_equiv (μ := cubeVolume d) (gridAffineEquiv k hk c) f
  simp only [gridAffineEquiv_apply] at h
  rw [← h]
  change (∫ z, f z ∂(cubeVolume d).map (gridAffine k c)) = _
  rw [gridAffine_map_cubeVolume k hk c, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem gridAffine_ae_pullback {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k)
    {P : Covariate d → Prop} (hP : ∀ᵐ z ∂cubeVolume d, P z) :
    ∀ᵐ w ∂cubeVolume d, P (gridAffine k c w) := by
  apply ae_of_ae_map (gridAffineEquiv k hk c).measurable.aemeasurable
  change ∀ᵐ z ∂(cubeVolume d).map (gridAffine k c), P z
  rw [gridAffine_map_cubeVolume k hk c]
  exact Measure.ae_smul_measure
    (ae_restrict_of_ae_restrict_of_subset (gridClosedBox_subset_cube k hk c) hP) _

def gridNormalizedAnchor {d : ℕ} (k : ℕ) (hk : 0 < k) (x : Covariate d) : Covariate d :=
  fun i => (k : ℝ) * (x i - regularGridCorner k (regularGridCell k hk x) i)

theorem gridNormalizedAnchor_mem_cube {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Covariate d) (hx : x ∈ unitCube d) : gridNormalizedAnchor k hk x ∈ unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  intro i
  have hlo := regular_grid_cell_corner_le k hk x hx i
  have hhi := (abs_le.mp (regular_grid_cell_radius k hk x hx i)).2
  constructor
  · exact mul_nonneg hkr.le (sub_nonneg.mpr hlo)
  · change (k : ℝ) * (x i - regularGridCorner k (regularGridCell k hk x) i) ≤ 1
    exact (mul_le_mul_of_nonneg_left hhi hkr.le).trans_eq (by field_simp)

theorem dyadicAnchoredFeature_affine {d ℓ : ℕ} (j : ℕ) (x w : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature j x
      (gridAffine ((2 : ℕ) ^ j) (regularGridCell _ (by positivity) x) w) γ =
      anchoredFeature (gridNormalizedAnchor ((2 : ℕ) ^ j) (by positivity) x) w γ := by
  unfold dyadicAnchoredFeature anchoredFeature
  congr 1
  funext i
  simp only [gridAffine, gridNormalizedAnchor, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  have hn : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

theorem regular_grid_index_eq_of_box (k : ℕ) (hk : 0 < k) (c : Fin k) (z : ℝ)
    (hlo : (c : ℝ) / k ≤ z) (hhi : z < (c : ℝ) / k + (k : ℝ)⁻¹) :
    regularGridIndex k hk z = c := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hz : 0 ≤ z := (div_nonneg (Nat.cast_nonneg _) hkr.le).trans hlo
  have hf : ⌊(k : ℝ) * z⌋₊ = c.val := by
    apply (Nat.floor_eq_iff (mul_nonneg hkr.le hz)).2
    constructor
    · have h := (div_le_iff₀ hkr).mp hlo
      nlinarith
    · have h := mul_lt_mul_of_pos_left hhi hkr
      have he : (k : ℝ) * ((c : ℝ) / k + (k : ℝ)⁻¹) = (c : ℝ) + 1 := by field_simp
      rwa [he] at h
  apply Fin.ext
  change min ⌊(k : ℝ) * z⌋₊ (k - 1) = c.val
  rw [hf, min_eq_left (by have := c.isLt; omega)]

/-- Grid fibers and closed affine boxes differ only on coordinate faces. -/
theorem regular_grid_fiber_ae_box {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    ((regularGridCell k hk) ⁻¹' {c} ∩ unitCube d) =ᵐ[volume] gridClosedBox k c := by
  have hfaces : ∀ᵐ z : Covariate d ∂volume,
      ∀ i, z i ≠ regularGridCorner k c i + (k : ℝ)⁻¹ := by
    rw [ae_all_iff]
    intro i
    apply ae_iff.mpr
    simp only [not_not]
    change (volume : Measure (Covariate d))
      ((fun z : Covariate d => z i) ⁻¹' {regularGridCorner k c i + (k : ℝ)⁻¹}) = 0
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null (fun _ : Fin d => (volume : Measure ℝ)) (measure_singleton _)
  filter_upwards [hfaces] with z hz
  apply propext
  constructor
  · intro hzcell
    have hc : regularGridCell k hk z = c := hzcell.1
    constructor <;> intro i
    · simpa only [hc] using regular_grid_cell_corner_le k hk z hzcell.2 i
    · have h := (abs_le.mp (regular_grid_cell_radius k hk z hzcell.2 i)).2
      simp only [hc] at h
      change z i ≤ regularGridCorner k c i + (k : ℝ)⁻¹
      simpa only [one_div] using (by linarith : z i ≤ regularGridCorner k c i + 1 / k)
  · intro hzbox
    refine ⟨?_, gridClosedBox_subset_cube k hk c hzbox⟩
    change regularGridCell k hk z = c
    funext i
    apply regular_grid_index_eq_of_box k hk (c i) (z i) (hzbox.1 i)
    exact lt_of_le_of_ne (hzbox.2 i) (hz i)

theorem regular_grid_fiber_restrict {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    (cubeVolume d).restrict ((regularGridCell k hk) ⁻¹' {c}) =
      volume.restrict (gridClosedBox k c) := by
  rw [cubeVolume, Measure.restrict_restrict
    ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))]
  exact Measure.restrict_congr_set (regular_grid_fiber_ae_box k hk c)

/-- The original cell integral, with the exact Jacobian and boundary convention. -/
theorem regular_grid_cell_integral {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k)
    (f : Covariate d → ℝ) :
    (k : ℝ) ^ d * (∫ z in (regularGridCell k hk) ⁻¹' {c}, f z ∂cubeVolume d) =
      ∫ w, f (gridAffine k c w) ∂cubeVolume d := by
  rw [regular_grid_fiber_restrict]
  exact (gridAffine_integral k hk c f).symm

end NearlyMinimax
