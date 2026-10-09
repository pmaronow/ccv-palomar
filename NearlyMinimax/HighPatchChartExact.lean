module

public import NearlyMinimax.HighPatchProductMeasure


@[expose] public section

/-! The exact torus chart Jacobian. Wrapping affine branches have disjoint
images after the null upper boundary of the unit cube is removed. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def highStrictUnitCube (d : ℕ) : Set (Covariate d) :=
  {x | ∀ r, 0 ≤ x r ∧ x r < 1}

def highWrapSector {d k : ℕ} (j : HighWindowLabels d k) (b : Fin d → Bool) :
    Set (Covariate d) :=
  {u | ∀ r, if b r then (j r).val = 0 ∧ u r < 0 else (j r).val = 0 → 0 ≤ u r}

theorem highWrapSector_measurable {d k : ℕ} (j : HighWindowLabels d k)
    (b : Fin d → Bool) : MeasurableSet (highWrapSector j b) := by
  unfold highWrapSector
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro r
  cases hb : b r
  · simp only [Bool.false_eq_true, if_false]
    by_cases hj : (j r).val = 0
    · simpa only [hj, true_implies] using measurableSet_le measurable_const (measurable_pi_apply r)
    · simp only [hj, false_implies, setOf_true, MeasurableSet.univ]
  · simp only [if_true]
    by_cases hj : (j r).val = 0
    · simpa only [hj, true_and] using measurableSet_lt (measurable_pi_apply r) measurable_const
    · simp only [hj, false_and, setOf_false, MeasurableSet.empty]

theorem highWrapSector_disjoint {d k : ℕ} (j : HighWindowLabels d k) :
    Pairwise (Disjoint on highWrapSector j) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro u hb hc
  obtain ⟨r,hr⟩ := not_forall.mp (fun h => hbc (funext h))
  have hbu := hb r
  have hcu := hc r
  cases hbr : b r <;> cases hcr : c r <;> simp only [hbr,hcr,if_true,if_false] at hbu hcu
  · exact hr (hbr.trans hcr.symm)
  · exact (not_lt_of_ge (hbu hcu.1)) hcu.2
  · exact (not_lt_of_ge (hcu hbu.1)) hbu.2
  · exact hr (hbr.trans hcr.symm)

theorem highUnitCube_strict_ae (d : ℕ) :
    unitCube d =ᵐ[(volume : Measure (Covariate d))] highStrictUnitCube d := by
  have hne : ∀ᵐ x : Covariate d ∂volume, ∀ r, x r ≠ 1 :=
    ae_all_iff.mpr (fun r => Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) r 1)
  filter_upwards [hne] with x hx
  apply propext
  change (∀ r, x r ∈ Icc (0 : ℝ) 1) ↔ ∀ r, 0 ≤ x r ∧ x r < 1
  constructor
  · intro h r
    exact ⟨(h r).1, lt_of_le_of_ne (h r).2 (hx r)⟩
  · intro h r
    exact ⟨(h r).1, (h r).2.le⟩

/-- The exact one-point torus patch chart domination has Jacobian k^-d;
there is no factor for wrapping branches. -/
theorem highLocalCoordinates_patch_map_le_exact {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) :
    Measure.map (highLocalCoordinates d k j)
      ((cubeVolume d).restrict (highTorusPatch d k j)) ≤
      ENNReal.ofReal ((1 / (k : ℝ))^d) • volume.restrict (spatialPatchBox d) := by
  have hbox : MeasurableSet (spatialPatchBox d) := measurableSet_Icc
  apply Measure.le_iff.mpr
  intro S hS
  let A := highLocalCoordinates d k j ⁻¹' S ∩ highTorusPatch d k j
  have hcover : A ∩ highStrictUnitCube d ⊆
      ⋃ b : Fin d → Bool, highAffineChart d k (highPatchWrapLift j b) ⁻¹'
        ((S ∩ spatialPatchBox d) ∩ highWrapSector j b) := by
    intro x hx
    obtain ⟨z,hz,hc⟩ := hx.1.2
    have hzcase (r : Fin d) : ∃ b : Bool,
        z r = if b then ((j r).val : ℤ)+(k : ℤ) else ((j r).val : ℤ) := by
      rcases highPatch_lift_cube_cases k hk (j r) (x r)
        ⟨(hx.2 r).1,(hx.2 r).2.le⟩ (z r) (hz r) (hc r) with h | h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    choose b hb using hzcase
    have hzb : z = highPatchWrapLift j b := by funext r; exact hb r
    have he := highLocalCoordinates_eq_affine_on_patch hk j hx.1.2 z hz hc
    apply Set.mem_iUnion.mpr
    refine ⟨b,?_⟩
    change highAffineChart d k (highPatchWrapLift j b) x ∈
      ((S ∩ spatialPatchBox d) ∩ highWrapSector j b)
    refine ⟨?_,?_⟩
    · rw [← hzb,← he]
      exact ⟨hx.1.1,highLocalCoordinates_patch_mem_box hk j hx.1.2⟩
    · intro r
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      cases hbr : b r
      · intro hj
        simpa only [highAffineChart,highPatchWrapLift,hbr,Bool.false_eq_true,if_false,hj,Int.ofNat_zero,
          Int.cast_zero,sub_zero] using mul_nonneg hkR.le (hx.2 r).1
      · simp only [hbr,if_true]
        have hu : (k : ℝ)*x r-z r < -((j r).val : ℝ) := by
          have hzR : (z r : ℝ) = ((j r).val : ℝ)+(k : ℝ) := by
            have hh := hb r
            simp only [hbr,if_true] at hh
            exact_mod_cast hh
          rw [hzR]
          nlinarith [mul_lt_mul_of_pos_left (hx.2 r).2 hkR]
        have hj : (j r).val = 0 := by
          by_contra h
          have hjR : (1 : ℝ) ≤ (j r).val := by exact_mod_cast (by omega : 1 ≤ (j r).val)
          linarith [(abs_lt.mp (hc r)).1]
        refine ⟨hj,?_⟩
        change (k : ℝ)*x r-(highPatchWrapLift j b r : ℝ) < 0
        rw [← hzb]
        simpa only [hj,Nat.cast_zero,neg_zero] using hu
  have hstrict : volume (A ∩ unitCube d) = volume (A ∩ highStrictUnitCube d) := by
    apply measure_congr
    filter_upwards [highUnitCube_strict_ae d] with x hx
    exact congrArg (fun h : Prop => x ∈ A ∧ h) hx
  have htarget (b : Fin d → Bool) :
      MeasurableSet ((S ∩ spatialPatchBox d) ∩ highWrapSector j b) :=
    (hS.inter hbox).inter (highWrapSector_measurable j b)
  have hdis : Pairwise (Disjoint on (fun b : Fin d → Bool =>
      (S ∩ spatialPatchBox d) ∩ highWrapSector j b)) := by
    intro b c hbc
    exact (highWrapSector_disjoint j hbc).mono Set.inter_subset_right Set.inter_subset_right
  rw [Measure.map_apply (highLocalCoordinates_measurable d k j) hS,
    Measure.restrict_apply ((highLocalCoordinates_measurable d k j) hS),
    cubeVolume,Measure.restrict_apply (((highLocalCoordinates_measurable d k j) hS).inter
      (highTorusPatch_measurableSet d k j)),Measure.smul_apply,
    Measure.restrict_apply hS,smul_eq_mul]
  change volume (A ∩ unitCube d) ≤ _
  rw [hstrict]
  calc
    _ ≤ volume (⋃ b : Fin d → Bool, highAffineChart d k (highPatchWrapLift j b) ⁻¹'
        ((S ∩ spatialPatchBox d) ∩ highWrapSector j b)) := measure_mono hcover
    _ ≤ ∑' b : Fin d → Bool, volume (highAffineChart d k (highPatchWrapLift j b) ⁻¹'
        ((S ∩ spatialPatchBox d) ∩ highWrapSector j b)) := measure_iUnion_le _
    _ = ∑' b : Fin d → Bool, ENNReal.ofReal (((k : ℝ)^d)⁻¹) *
        volume ((S ∩ spatialPatchBox d) ∩ highWrapSector j b) := by
      apply tsum_congr
      intro b
      rw [← Measure.map_apply (highAffineChart_measurable d k _) (htarget b),
        highAffineChart_map_volume d k (by omega) _,Measure.smul_apply,smul_eq_mul]
    _ = ENNReal.ofReal (((k : ℝ)^d)⁻¹) *
        volume (⋃ b : Fin d → Bool, (S ∩ spatialPatchBox d) ∩ highWrapSector j b) := by
      rw [ENNReal.tsum_mul_left,measure_iUnion hdis htarget]
    _ ≤ ENNReal.ofReal (((k : ℝ)^d)⁻¹) * volume (S ∩ spatialPatchBox d) := by
      gcongr
      exact iUnion_subset (fun _ => Set.inter_subset_left)
    _ = ENNReal.ofReal ((1/(k : ℝ))^d) * volume (S ∩ spatialPatchBox d) := by
      congr 1
      congr 1
      rw [one_div,inv_pow]

end NearlyMinimax
