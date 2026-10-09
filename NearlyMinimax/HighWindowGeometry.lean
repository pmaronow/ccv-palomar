module

public import NearlyMinimax.HighPeriodizedFrame


@[expose] public section

/-! Genuine torus patch volume and finite overlap graph bounds. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

def highTorusPatch (d k : ℕ) (j : HighWindowLabels d k) : Set (Covariate d) :=
  {x | ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
    ∀ r, |(k : ℝ) * x r - z r| < 1}

theorem highTorusPatch_measurableSet (d k : ℕ) (j : HighWindowLabels d k) :
    MeasurableSet (highTorusPatch d k j) := by
  unfold highTorusPatch
  simp_rw [setOf_exists]
  apply MeasurableSet.iUnion
  intro z
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · have he : {x : Covariate d | (∀ r, (z r : ZMod k) = j r) ∧
        ∀ r, |(k : ℝ) * x r - z r| < 1} =
        {x : Covariate d | ∀ r, |(k : ℝ) * x r - z r| < 1} := by
      ext x
      exact and_iff_right hz
    rw [he]
    simp_rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  · simp only [hz, false_and, setOf_false]
    exact MeasurableSet.empty

def highPatchCoordinate (k : ℕ) (j : ZMod k) : Set ℝ :=
  if j = 0 then Icc 0 (1 / (k : ℝ)) ∪ Icc (1 - 1 / (k : ℝ)) 1 else
    Icc (((j.val : ℝ) - 1) / k) (((j.val : ℝ) + 1) / k)

theorem highPatchCoordinate_measurableSet (k : ℕ) (j : ZMod k) :
    MeasurableSet (highPatchCoordinate k j) := by
  unfold highPatchCoordinate
  split_ifs
  · exact measurableSet_Icc.union measurableSet_Icc
  · exact measurableSet_Icc

theorem highPatchCoordinate_volume_le (k : ℕ) (hk : 0 < k) (j : ZMod k) :
    volume (highPatchCoordinate k j) ≤ ENNReal.ofReal (2 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold highPatchCoordinate
  split_ifs
  · calc
      _ ≤ volume (Icc (0 : ℝ) (1 / k)) + volume (Icc (1 - 1 / (k : ℝ)) 1) :=
        measure_union_le _ _
      _ = ENNReal.ofReal (1 / (k : ℝ)) + ENNReal.ofReal (1 / (k : ℝ)) := by
        rw [Real.volume_Icc, Real.volume_Icc]
        congr 1 <;> congr 1 <;> ring
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    ring_nf
    exact le_rfl

theorem highPatchCoordinate_contains_lift (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : ZMod k) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (z : ℤ)
    (hz : (z : ZMod k) = j) (hclose : |(k : ℝ) * x - z| < 1) :
    x ∈ highPatchCoordinate k j := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkv : (j.val : ℤ) < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ (k : ℤ) := by
    have h := abs_lt.mp hclose
    have hzL : (-1 : ℝ) < z := by nlinarith [mul_nonneg hkR.le hx.1]
    have hzU : (z : ℝ) < k + 1 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
    have hzLZ : (-1 : ℤ) < z := by exact_mod_cast hzL
    have hzUZ : z < (k : ℤ) + 1 := by exact_mod_cast hzU
    omega
  have hqs : q = 0 ∨ q = 1 := by
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
  have hcl := abs_lt.mp hclose
  rcases hqs with hq0 | hq1
  · have hzval : z = (j.val : ℤ) := by simpa only [hq0, mul_zero, add_zero] using hq
    have hzvalR : (z : ℝ) = j.val := by exact_mod_cast hzval
    unfold highPatchCoordinate
    split_ifs with hj
    · apply Or.inl
      rw [hj] at hzvalR
      simp only [ZMod.val_zero, Nat.cast_zero] at hzvalR
      refine ⟨hx.1, ?_⟩
      apply (le_div_iff₀ hkR).mpr
      nlinarith
    · constructor
      · apply (div_le_iff₀ hkR).mpr
        nlinarith
      · apply (le_div_iff₀ hkR).mpr
        nlinarith
  · have hjval : j.val = 0 := by rw [hq1, mul_one] at hq; omega
    have hj : j = 0 := by
      have hv := ZMod.natCast_zmod_val j
      rw [hjval, Nat.cast_zero] at hv
      exact hv.symm
    have hzR : (z : ℝ) = k := by
      have hz' : z = (k : ℤ) := by simp only [hjval, Nat.cast_zero, hq1, mul_one, zero_add] at hq; exact hq
      exact_mod_cast hz'
    unfold highPatchCoordinate
    rw [ite_eq_left hj]
    apply Or.inr
    refine ⟨?_, hx.2⟩
    have hr : ((k : ℝ) - 1) / k ≤ x := (div_le_iff₀ hkR).mpr (by nlinarith)
    convert hr using 1
    field_simp

theorem highTorusPatch_cube_subset (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) :
    highTorusPatch d k j ∩ unitCube d ⊆
      Set.pi Set.univ (fun r => highPatchCoordinate k (j r)) := by
  intro x hx r hr
  obtain ⟨z, hz, hclose⟩ := hx.1
  exact highPatchCoordinate_contains_lift k hk (j r) (x r) (hx.2 r) (z r) (hz r) (hclose r)

/-- The genuine torus patch, including patches wrapping across the
boundary of the unit cube, has the manuscript's volume bound. -/
theorem highTorusPatch_volume_le (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) :
    cubeVolume d (highTorusPatch d k j) ≤ ENNReal.ofReal (2 / (k : ℝ)) ^ d := by
  rw [cubeVolume, Measure.restrict_apply (highTorusPatch_measurableSet d k j)]
  calc
    _ ≤ volume (Set.pi Set.univ (fun r => highPatchCoordinate k (j r))) :=
      measure_mono (highTorusPatch_cube_subset d k hk j)
    _ = ∏ r, volume (highPatchCoordinate k (j r)) := volume_pi_pi _
    _ ≤ ∏ _r : Fin d, ENNReal.ofReal (2 / (k : ℝ)) :=
      Finset.prod_le_prod (fun r _ => highPatchCoordinate_volume_le k (by omega) (j r))
    _ = _ := by simp

def highNeighborLabels (d k : ℕ) (j : HighWindowLabels d k) : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {j r - 1, j r, j r + 1})

theorem highNeighborLabels_card_le (d k : ℕ) [NeZero k] (j : HighWindowLabels d k) :
    (highNeighborLabels d k j).card ≤ 3 ^ d := by
  rw [highNeighborLabels, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 3 := Finset.prod_le_prod' (fun r _ => Finset.card_le_three)
    _ = _ := by simp

theorem highNeighborLabels_self_mem (d k : ℕ) (j : HighWindowLabels d k) :
    j ∈ highNeighborLabels d k j := by
  apply Fintype.mem_piFinset.mpr
  intro r
  simp

theorem highNeighborLabels_symmetric (d k : ℕ) (j l : HighWindowLabels d k)
    (h : l ∈ highNeighborLabels d k j) : j ∈ highNeighborLabels d k l := by
  apply Fintype.mem_piFinset.mpr
  intro r
  have hr := Fintype.mem_piFinset.mp h r
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
  rcases hr with hr | hr | hr
  · right
    right
    rw [hr]
    ring
  · right
    left
    exact hr.symm
  · left
    rw [hr]
    ring

theorem highNeighborLabels_erase_card_le (d k : ℕ) [NeZero k]
    (j : HighWindowLabels d k) :
    ((highNeighborLabels d k j).erase j).card ≤ 3 ^ d - 1 := by
  rw [Finset.card_erase_of_mem (highNeighborLabels_self_mem d k j)]
  exact Nat.sub_le_sub_right (highNeighborLabels_card_le d k j) 1

theorem highTorusPatch_intersects_neighbor (d k : ℕ) [NeZero k]
    (j l : HighWindowLabels d k) (h : (highTorusPatch d k j ∩ highTorusPatch d k l).Nonempty) :
    l ∈ highNeighborLabels d k j := by
  obtain ⟨x, ⟨z, hz, hc⟩, ⟨q, hq, hd⟩⟩ := h
  apply Fintype.mem_piFinset.mpr
  intro r
  have hdiff : |(q r : ℝ) - z r| < 2 := by
    have hh := abs_sub_le (q r : ℝ) ((k : ℝ) * x r) (z r : ℝ)
    have hds : |(q r : ℝ) - (k : ℝ) * x r| < 1 := by
      rw [abs_sub_comm]
      exact hd r
    exact hh.trans_lt (by linarith [hc r])
  have hdiffZ : -1 ≤ q r - z r ∧ q r - z r ≤ 1 := by
    have hh := abs_lt.mp hdiff
    have hL : (-2 : ℤ) < q r - z r := by exact_mod_cast hh.1
    have hU : q r - z r < (2 : ℤ) := by exact_mod_cast hh.2
    omega
  have hqcases : q r = z r - 1 ∨ q r = z r ∨ q r = z r + 1 := by omega
  rcases hqcases with he | he | he
  · have he' : l r = j r - 1 := by rw [← hq r, he, Int.cast_sub, ← hz r]; simp
    simp only [he', Finset.mem_insert, true_or]
  · have he' : l r = j r := by rw [← hq r, he, hz r]
    simp only [he', Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · have he' : l r = j r + 1 := by rw [← hq r, he, Int.cast_add, ← hz r]; simp
    simp only [he', Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

theorem highTorusPatch_disjoint_of_not_neighbor (d k : ℕ) [NeZero k]
    (j l : HighWindowLabels d k) (h : l ∉ highNeighborLabels d k j) :
    Disjoint (highTorusPatch d k j) (highTorusPatch d k l) := by
  exact Set.disjoint_left.mpr (fun x hj hl =>
    h (highTorusPatch_intersects_neighbor d k j l ⟨x, hj, hl⟩))

theorem highFrame_chart_derivative_supported_patch (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (P : MvPolynomial (Fin d) ℝ) (q : ℕ) :
    support (iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile P))) ⊆
      highTorusPatch d k j := by
  intro x hx
  obtain ⟨z, hz, hclose⟩ := highPeriodizedChart_derivative_support_lift d k hk j
    (highFrameProfile P) (highFrameProfile_zero_of_window_zero P) q x hx
  refine ⟨z, hz, ?_⟩
  intro r
  exact (hclose r).trans_lt (by norm_num)

theorem highPeriodicTensor_supported_patch (d k : ℕ) (j : HighWindowLabels d k) :
    support (highPeriodicTensor d k j) ⊆ highTorusPatch d k j := by
  intro x hx
  obtain ⟨z, hz, hclose⟩ := highPeriodicTensor_support_lift d k j x hx
  refine ⟨z, hz, ?_⟩
  intro r
  exact (hclose r).trans (by norm_num)

theorem highPeriodizedChart_integer_periodic (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (v : Fin d → ℤ) (x : Covariate d) :
    highPeriodizedChart d k j G (fun r => x r + v r) = highPeriodizedChart d k j G x := by
  let b : Fin d → ℤ := fun r => (k : ℤ) * v r
  unfold highPeriodizedChart
  calc
    _ = ∑ᶠ z : Fin d → ℤ, if (∀ r, ((z - b) r : ZMod k) = j r) then
        G (fun r => (k : ℝ) * x r - (z - b) r) else 0 := by
      apply finsum_congr
      intro z
      have hres : (∀ r, ((z - b) r : ZMod k) = j r) ↔ ∀ r, (z r : ZMod k) = j r := by
        simp only [Pi.sub_apply, b, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
          ZMod.natCast_self, zero_mul, sub_zero]
      simp only [hres]
      congr 2
      funext r
      simp only [Pi.sub_apply, b]
      push_cast
      ring
    _ = _ := finsum_comp (g := fun z : Fin d → ℤ => if (∀ r, (z r : ZMod k) = j r) then
        G (fun r => (k : ℝ) * x r - z r) else 0) (fun z => z - b) (by
      constructor
      · intro z q h
        simpa only [sub_left_inj] using h
      · intro z
        exact ⟨z + b, by simp⟩)

theorem highFrameField_integer_periodic (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) (v : Fin d → ℤ) (x : Covariate d) :
    highFrameField d k η P (fun r => x r + v r) = highFrameField d k η P x := by
  unfold highFrameField
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact highPeriodizedChart_integer_periodic d k j (highFrameProfile (P j)) v x

end NearlyMinimax
