module

public import NearlyMinimax.LowSmoothnessPrior


@[expose] public section

/-! # Normalized tent windows for the order-zero lower bound

The manuscript uses smooth periodic compact bumps. For `0 < s ≤ 1` only
continuity and Hölder bounds are required. Normalized finite-grid tents,
extended by coordinate clamping, provide an alternative globally continuous
partition with local support on the design cube.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

def clampUnit (x : ℝ) : ℝ := min 1 (max 0 x)

theorem clampUnit_mem (x : ℝ) : clampUnit x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem clampUnit_eq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : clampUnit x = x := by
  simp [clampUnit, max_eq_right hx.1, min_eq_right hx.2]

theorem clampUnit_continuous : Continuous clampUnit := by
  unfold clampUnit
  fun_prop

def gridTent (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : ℝ :=
  max 0 (1 - |(k : ℝ) * clampUnit x - j.val|)

theorem gridTent_nonneg (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : 0 ≤ gridTent k j x :=
  le_max_left _ _

theorem gridTent_le_one (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : gridTent k j x ≤ 1 := by
  unfold gridTent
  exact max_le (by norm_num) (by linarith [abs_nonneg ((k : ℝ) * clampUnit x - j.val)])

theorem gridTent_continuous (k : ℕ) (j : Fin (k + 1)) : Continuous (gridTent k j) := by
  unfold gridTent clampUnit
  fun_prop

/-- A nearest grid index has tent value at least one half, globally. -/
theorem gridTent_cover (k : ℕ) (x : ℝ) :
    ∃ j : Fin (k + 1), (1 / 2 : ℝ) ≤ gridTent k j x := by
  let t := (k : ℝ) * clampUnit x
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1
  have htk : t ≤ k := by
    simpa [t] using mul_le_mul_of_nonneg_left (clampUnit_mem x).2 (Nat.cast_nonneg k)
  let j := Nat.floor (t + 1 / 2)
  have hfloor : (j : ℝ) ≤ t + 1 / 2 := Nat.floor_le (by linarith)
  have hlt : t + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjk : j ≤ k := by
    by_contra h
    have hj : (k : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : k + 1 ≤ j)
    linarith
  refine ⟨⟨j, by omega⟩, ?_⟩
  have hdist : |t - j| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  exact le_trans (by simpa [t] using (show (1 / 2 : ℝ) ≤ 1 - |t - j| by linarith))
    (le_max_right _ _)

def gridTentEnergy (k : ℕ) (x : ℝ) : ℝ := ∑ j : Fin (k + 1), gridTent k j x ^ 2

theorem gridTentEnergy_lower (k : ℕ) (x : ℝ) : (1 / 4 : ℝ) ≤ gridTentEnergy k x := by
  obtain ⟨j, hj⟩ := gridTent_cover k x
  have hsq : (1 / 4 : ℝ) ≤ gridTent k j x ^ 2 := by nlinarith
  exact hsq.trans (Finset.single_le_sum (fun i _ => sq_nonneg (gridTent k i x)) (Finset.mem_univ j))

theorem gridTentEnergy_pos (k : ℕ) (x : ℝ) : 0 < gridTentEnergy k x :=
  lt_of_lt_of_le (by norm_num) (gridTentEnergy_lower k x)

theorem gridTentEnergy_continuous (k : ℕ) : Continuous (gridTentEnergy k) :=
  continuous_finsetSum _ (fun j _ => (gridTent_continuous k j).pow 2)

def gridWindow (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : ℝ :=
  gridTent k j x / Real.sqrt (gridTentEnergy k x)

theorem gridWindow_nonneg (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : 0 ≤ gridWindow k j x :=
  div_nonneg (gridTent_nonneg k j x) (Real.sqrt_nonneg _)

theorem gridWindow_continuous (k : ℕ) (j : Fin (k + 1)) : Continuous (gridWindow k j) := by
  exact (gridTent_continuous k j).div (gridTentEnergy_continuous k).sqrt
    (fun x => ne_of_gt (Real.sqrt_pos.mpr (gridTentEnergy_pos k x)))

/-- The normalized windows form an exact squared partition of unity. -/
theorem gridWindow_square_partition (k : ℕ) (x : ℝ) :
    (∑ j : Fin (k + 1), gridWindow k j x ^ 2) = 1 := by
  simp only [gridWindow, div_pow, Real.sq_sqrt (gridTentEnergy_pos k x).le]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gridTentEnergy_pos k x))

theorem gridWindow_le_one (k : ℕ) (j : Fin (k + 1)) (x : ℝ) : gridWindow k j x ≤ 1 := by
  have hs : gridWindow k j x ^ 2 ≤ 1 := by
    rw [← gridWindow_square_partition k x]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (gridWindow k i x)) (Finset.mem_univ j)
  nlinarith [gridWindow_nonneg k j x]

def gridTensorWindow (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d) : ℝ :=
  ∏ i, gridWindow k (j i) (x i)

theorem gridTensorWindow_continuous (d k : ℕ) (j : Fin d → Fin (k + 1)) :
    Continuous (gridTensorWindow d k j) :=
  continuous_finsetProd _ (fun i _ => (gridWindow_continuous k (j i)).comp (continuous_apply i))

theorem gridTensorWindow_nonneg (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d) :
    0 ≤ gridTensorWindow d k j x := Finset.prod_nonneg (fun i _ => gridWindow_nonneg k (j i) (x i))

theorem gridTensorWindow_le_one (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d) :
    gridTensorWindow d k j x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => gridWindow_nonneg k (j i) (x i))
    (fun i _ => gridWindow_le_one k (j i) (x i))

theorem gridTensorWindow_square_partition (d k : ℕ) (x : Covariate d) :
    (∑ j : Fin d → Fin (k + 1), gridTensorWindow d k j x ^ 2) = 1 := by
  simp only [gridTensorWindow, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (j : Fin (k + 1)) => gridWindow k j (x i) ^ 2)]
  simp [gridWindow_square_partition]

def gridTentActive (k : ℕ) (x : ℝ) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun j => gridTent k j x ≠ 0)

private theorem gridTent_active_indices (k : ℕ) (x : ℝ) (j : Fin (k + 1))
    (hj : j ∈ gridTentActive k x) :
    j.val = Nat.floor ((k : ℝ) * clampUnit x) ∨
      j.val = Nat.floor ((k : ℝ) * clampUnit x) + 1 := by
  let t := (k : ℝ) * clampUnit x
  let m := Nat.floor t
  have hne : gridTent k j x ≠ 0 := (Finset.mem_filter.mp hj).2
  have hd : |t - j.val| < 1 := by
    by_contra h
    have he : gridTent k j x = 0 := max_eq_left (by dsimp [t] at h; linarith)
    exact hne he
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1
  have hm : (m : ℝ) ≤ t := Nat.floor_le ht0
  have hlt : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
  have hlow : m ≤ j.val := by
    by_contra h
    have hcast : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : j.val + 1 ≤ m)
    linarith [(abs_lt.mp hd).2]
  have hhigh : j.val ≤ m + 1 := by
    by_contra h
    have hcast : (m : ℝ) + 2 ≤ j.val := by exact_mod_cast (by omega : m + 2 ≤ j.val)
    linarith [(abs_lt.mp hd).1]
  change j.val = m ∨ j.val = m + 1
  omega

/-- At most two one-dimensional tents are nonzero at any point. -/
theorem gridTent_active_card (k : ℕ) (x : ℝ) : (gridTentActive k x).card ≤ 2 := by
  have hsub : (gridTentActive k x).image Fin.val ⊆
      {Nat.floor ((k : ℝ) * clampUnit x), Nat.floor ((k : ℝ) * clampUnit x) + 1} := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    rcases gridTent_active_indices k x i hi with h | h <;> simp [h]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  exact hcard.trans (by simp)

theorem gridWindow_eq_zero_iff (k : ℕ) (j : Fin (k + 1)) (x : ℝ) :
    gridWindow k j x = 0 ↔ gridTent k j x = 0 := by
  simp only [gridWindow, div_eq_zero_iff, ne_of_gt (Real.sqrt_pos.mpr (gridTentEnergy_pos k x)),
    or_false]

def gridTensorActive (d k : ℕ) (x : Covariate d) : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridTentActive k (x i))

theorem gridTensorWindow_eq_zero_of_not_active (d k : ℕ) (j : Fin d → Fin (k + 1))
    (x : Covariate d) (hj : j ∉ gridTensorActive d k x) : gridTensorWindow d k j x = 0 := by
  have hnot : ¬∀ i, j i ∈ gridTentActive k (x i) := by
    simpa [gridTensorActive, Fintype.mem_piFinset] using hj
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hz : gridWindow k (j i) (x i) = 0 := by
    apply (gridWindow_eq_zero_iff k (j i) (x i)).mpr
    simpa [gridTentActive] using hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem gridTensor_active_card (d k : ℕ) (x : Covariate d) : (gridTensorActive d k x).card ≤ 2 ^ d := by
  rw [gridTensorActive, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 2 := Finset.prod_le_prod (fun i _ => gridTent_active_card k (x i))
    _ = _ := by simp

theorem clampUnit_modulus (x y : ℝ) : |clampUnit x - clampUnit y| ≤ |x - y| := by
  have hmax : |max 0 x - max 0 y| ≤ |x - y| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] using
      abs_max_sub_max_le_max (0 : ℝ) x 0 y
  have hmin : |clampUnit x - clampUnit y| ≤ |max 0 x - max 0 y| := by
    simpa only [clampUnit, sub_self, abs_zero,
      max_eq_right (abs_nonneg (max 0 x - max 0 y))] using
      abs_min_sub_min_le_max (1 : ℝ) (max 0 x) 1 (max 0 y)
  exact hmin.trans hmax

theorem gridTent_modulus (k : ℕ) (j : Fin (k + 1)) (x y : ℝ) :
    |gridTent k j x - gridTent k j y| ≤ (k : ℝ) * |x - y| := by
  have hmax : |gridTent k j x - gridTent k j y| ≤
      abs (|(k : ℝ) * clampUnit x - j.val| - |(k : ℝ) * clampUnit y - j.val|) := by
    have h := abs_max_sub_max_le_max (0 : ℝ)
      (1 - |(k : ℝ) * clampUnit x - j.val|) 0 (1 - |(k : ℝ) * clampUnit y - j.val|)
    have hr : max 0 |(1 - |(k : ℝ) * clampUnit x - j.val|) -
        (1 - |(k : ℝ) * clampUnit y - j.val|)| =
        abs (|(k : ℝ) * clampUnit x - j.val| - |(k : ℝ) * clampUnit y - j.val|) := by
      rw [max_eq_right (abs_nonneg _), sub_sub_sub_cancel_left, abs_sub_comm]
    simpa only [gridTent, sub_self, abs_zero, hr] using h
  calc
    _ ≤ abs (|(k : ℝ) * clampUnit x - j.val| - |(k : ℝ) * clampUnit y - j.val|) := hmax
    _ ≤ |((k : ℝ) * clampUnit x - j.val) - ((k : ℝ) * clampUnit y - j.val)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = (k : ℝ) * |clampUnit x - clampUnit y| := by
      rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (clampUnit_modulus x y) (Nat.cast_nonneg k)

/-- The normalization energy has a scale-correct uniform Lipschitz bound. -/
theorem gridTentEnergy_modulus (k : ℕ) (x y : ℝ) :
    |gridTentEnergy k x - gridTentEnergy k y| ≤ 8 * k * |x - y| := by
  let S := gridTentActive k x ∪ gridTentActive k y
  have hcard : S.card ≤ 4 := (Finset.card_union_le _ _).trans
    (by have hx := gridTent_active_card k x; have hy := gridTent_active_card k y; omega)
  have hzero (j : Fin (k + 1)) (hj : j ∉ S) :
      gridTent k j x ^ 2 - gridTent k j y ^ 2 = 0 := by
    have hx : gridTent k j x = 0 := by
      have : j ∉ gridTentActive k x := fun h => hj (Finset.mem_union_left _ h)
      simpa [gridTentActive] using this
    have hy : gridTent k j y = 0 := by
      have : j ∉ gridTentActive k y := fun h => hj (Finset.mem_union_right _ h)
      simpa [gridTentActive] using this
    simp [hx, hy]
  have hpoint (j : Fin (k + 1)) :
      |gridTent k j x ^ 2 - gridTent k j y ^ 2| ≤ 2 * k * |x - y| := by
    have hx0 := gridTent_nonneg k j x
    have hy0 := gridTent_nonneg k j y
    have hx1 := gridTent_le_one k j x
    have hy1 := gridTent_le_one k j y
    rw [show gridTent k j x ^ 2 - gridTent k j y ^ 2 =
      (gridTent k j x - gridTent k j y) * (gridTent k j x + gridTent k j y) by ring,
      abs_mul, abs_of_nonneg (add_nonneg hx0 hy0)]
    nlinarith [gridTent_modulus k j x y, abs_nonneg (gridTent k j x - gridTent k j y),
      mul_nonneg (sub_nonneg.mpr (gridTent_modulus k j x y)) (add_nonneg hx0 hy0)]
  change |(∑ j, gridTent k j x ^ 2) - (∑ j, gridTent k j y ^ 2)| ≤ _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ S)
    (fun j _ hj => hzero j hj)]
  calc
    _ ≤ ∑ j ∈ S, |gridTent k j x ^ 2 - gridTent k j y ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S, 2 * (k : ℝ) * |x - y| := Finset.sum_le_sum (fun j _ => hpoint j)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcast : (S.card : ℝ) ≤ 4 := by exact_mod_cast hcard
      nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]

theorem gridTentEnergy_sqrt_lower (k : ℕ) (x : ℝ) :
    (1 / 2 : ℝ) ≤ Real.sqrt (gridTentEnergy k x) := by
  nlinarith [Real.sqrt_nonneg (gridTentEnergy k x),
    Real.sq_sqrt (gridTentEnergy_pos k x).le, gridTentEnergy_lower k x]

theorem gridTentEnergy_sqrt_modulus (k : ℕ) (x y : ℝ) :
    |Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y)| ≤ 8 * k * |x - y| := by
  have hx := gridTentEnergy_sqrt_lower k x
  have hy := gridTentEnergy_sqrt_lower k y
  have hid : |gridTentEnergy k x - gridTentEnergy k y| =
      |Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y)| *
        (Real.sqrt (gridTentEnergy k x) + Real.sqrt (gridTentEnergy k y)) := by
    conv_lhs => rw [← Real.sq_sqrt (gridTentEnergy_pos k x).le, ← Real.sq_sqrt (gridTentEnergy_pos k y).le]
    rw [show Real.sqrt (gridTentEnergy k x) ^ 2 - Real.sqrt (gridTentEnergy k y) ^ 2 =
      (Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y)) *
        (Real.sqrt (gridTentEnergy k x) + Real.sqrt (gridTentEnergy k y)) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg (gridTentEnergy k x))
        (Real.sqrt_nonneg (gridTentEnergy k y)))]
  have hb := gridTentEnergy_modulus k x y
  rw [hid] at hb
  nlinarith [abs_nonneg (Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y))]

theorem gridWindow_modulus (k : ℕ) (j : Fin (k + 1)) (x y : ℝ) :
    |gridWindow k j x - gridWindow k j y| ≤ 34 * k * |x - y| := by
  let A := Real.sqrt (gridTentEnergy k x)
  let B := Real.sqrt (gridTentEnergy k y)
  have hA : (1 / 2 : ℝ) ≤ A := gridTentEnergy_sqrt_lower k x
  have hB : (1 / 2 : ℝ) ≤ B := gridTentEnergy_sqrt_lower k y
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hAB : (1 / 4 : ℝ) ≤ A * B := by nlinarith
  have hroot : |B - A| ≤ 8 * k * |x - y| := by
    simpa only [abs_sub_comm] using gridTentEnergy_sqrt_modulus k x y
  have hfirst : |(gridTent k j x - gridTent k j y) / A| ≤ 2 * k * |x - y| := by
    rw [abs_div, abs_of_pos hAp]
    apply (div_le_iff₀ hAp).mpr
    have htent := gridTent_modulus k j x y
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]
  have hsecond : |gridTent k j y * (B - A) / (A * B)| ≤ 32 * k * |x - y| := by
    rw [abs_div, abs_mul, abs_of_nonneg (gridTent_nonneg k j y), abs_of_pos (mul_pos hAp hBp)]
    apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
    have htent := gridTent_le_one k j y
    have hnonneg := gridTent_nonneg k j y
    have habs := abs_nonneg (B - A)
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y)),
      mul_nonneg (sub_nonneg.mpr htent) habs]
  have hid : gridWindow k j x - gridWindow k j y =
      (gridTent k j x - gridTent k j y) / A + gridTent k j y * (B - A) / (A * B) := by
    change gridTent k j x / A - gridTent k j y / B = _
    field_simp [ne_of_gt hAp, ne_of_gt hBp]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

private theorem bounded_product_modulus {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hp : |∏ j ∈ s, f j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hh := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    have hgi := hg i (Finset.mem_insert_self _ _)
    rw [show f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j) =
      (f i - g i) * (∏ j ∈ s, f j) + g i * ((∏ j ∈ s, f j) - (∏ j ∈ s, g j)) by ring]
    calc
      _ ≤ |(f i - g i) * (∏ j ∈ s, f j)| +
          |g i * ((∏ j ∈ s, f j) - (∏ j ∈ s, g j))| := abs_add_le _ _
      _ ≤ |f i - g i| + ∑ j ∈ s, |f j - g j| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (by nlinarith [abs_nonneg (f i - g i)])
          (by simpa only [one_mul] using mul_le_mul hgi hh (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))

theorem coordinate_abs_le_euclideanNorm {d : ℕ} (x : Covariate d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  have hs : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have he : euclideanNorm x ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hn : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  nlinarith [sq_abs (x i), abs_nonneg (x i)]

theorem gridTensorWindow_modulus (d k : ℕ) (j : Fin d → Fin (k + 1)) (x y : Covariate d) :
    |gridTensorWindow d k j x - gridTensorWindow d k j y| ≤
      34 * k * d * euclideanNorm (x - y) := by
  have hh := bounded_product_modulus (Finset.univ : Finset (Fin d))
    (fun i => gridWindow k (j i) (x i)) (fun i => gridWindow k (j i) (y i))
    (fun i _ => by rw [abs_of_nonneg (gridWindow_nonneg k (j i) (x i))]; exact gridWindow_le_one k (j i) (x i))
    (fun i _ => by rw [abs_of_nonneg (gridWindow_nonneg k (j i) (y i))]; exact gridWindow_le_one k (j i) (y i))
  calc
    _ ≤ ∑ i, |gridWindow k (j i) (x i) - gridWindow k (j i) (y i)| := hh
    _ ≤ ∑ _i : Fin d, 34 * (k : ℝ) * euclideanNorm (x - y) := by
      apply Finset.sum_le_sum
      intro i _
      exact (gridWindow_modulus k (j i) (x i) (y i)).trans
        (mul_le_mul_of_nonneg_left (coordinate_abs_le_euclideanNorm (x - y) i) (by positivity))
    _ = _ := by simp; ring

def gridPriorField (d k : ℕ) (η : ℝ) (ξ : (Fin d → Fin (k + 1)) → Fin 3)
    (x : Covariate d) : ℝ :=
  η * ∑ j, gridTensorWindow d k j x * ternaryValue 1 (ξ j)

theorem gridPriorField_continuous (d k : ℕ) (η : ℝ)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) : Continuous (gridPriorField d k η ξ) :=
  (continuous_finsetSum _ (fun j _ => (gridTensorWindow_continuous d k j).mul_const _)).const_mul _

theorem ternaryValue_one_abs_le (y : Fin 3) : |ternaryValue 1 y| ≤ 1 := by
  fin_cases y <;> norm_num [ternaryValue]

theorem gridPriorField_abs_bound (d k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) (x : Covariate d) :
    |gridPriorField d k η ξ x| ≤ (2 : ℝ) ^ d * η := by
  have heq : (∑ j, gridTensorWindow d k j x * ternaryValue 1 (ξ j)) =
      ∑ j ∈ gridTensorActive d k x, gridTensorWindow d k j x * ternaryValue 1 (ξ j) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [gridTensorWindow_eq_zero_of_not_active d k j x hj]
  rw [gridPriorField, abs_mul, abs_of_nonneg hη, heq]
  have hsum : |∑ j ∈ gridTensorActive d k x,
      gridTensorWindow d k j x * ternaryValue 1 (ξ j)| ≤ (2 : ℝ) ^ d := by
    calc
      _ ≤ ∑ j ∈ gridTensorActive d k x, |gridTensorWindow d k j x * ternaryValue 1 (ξ j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ gridTensorActive d k x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (gridTensorWindow_nonneg d k j x)]
        simpa only [one_mul] using mul_le_mul (gridTensorWindow_le_one d k j x)
          (ternaryValue_one_abs_le (ξ j)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast gridTensor_active_card d k x
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsum hη

theorem gridPriorField_lipschitz_bound (d k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) (x y : Covariate d) :
    |gridPriorField d k η ξ x - gridPriorField d k η ξ y| ≤
      (68 * (2 : ℝ) ^ d * (d + 1)) * η * k * euclideanNorm (x - y) := by
  let S := gridTensorActive d k x ∪ gridTensorActive d k y
  have hcard : (S.card : ℝ) ≤ 2 * (2 : ℝ) ^ d := by
    have h := (Finset.card_union_le (gridTensorActive d k x) (gridTensorActive d k y)).trans
      (Nat.add_le_add (gridTensor_active_card d k x) (gridTensor_active_card d k y))
    have hcast : ((gridTensorActive d k x ∪ gridTensorActive d k y).card : ℝ) ≤
        (2 : ℝ) ^ d + (2 : ℝ) ^ d := by exact_mod_cast h
    simpa only [S, two_mul] using hcast
  have hzero (j : Fin d → Fin (k + 1)) (hj : j ∉ S) :
      (gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ j) = 0 := by
    have hx := gridTensorWindow_eq_zero_of_not_active d k j x
      (fun h => hj (Finset.mem_union_left _ h))
    have hy := gridTensorWindow_eq_zero_of_not_active d k j y
      (fun h => hj (Finset.mem_union_right _ h))
    simp [hx, hy]
  have hn : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
  have hpoint (j : Fin d → Fin (k + 1)) :
      |(gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ j)| ≤
        34 * k * d * euclideanNorm (x - y) := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (gridTensorWindow_modulus d k j x y)
      (ternaryValue_one_abs_le (ξ j)) (abs_nonneg _) (by positivity :
        0 ≤ 34 * (k : ℝ) * d * euclideanNorm (x - y))
  have hsum : |∑ j ∈ S, (gridTensorWindow d k j x - gridTensorWindow d k j y) *
      ternaryValue 1 (ξ j)| ≤ 68 * (2 : ℝ) ^ d * (d + 1) * k * euclideanNorm (x - y) := by
    calc
      _ ≤ ∑ j ∈ S, |(gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ S, 34 * (k : ℝ) * d * euclideanNorm (x - y) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = (S.card : ℝ) * (34 * k * d * euclideanNorm (x - y)) := by simp
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hcard
          (by positivity : 0 ≤ 34 * (k : ℝ) * d * euclideanNorm (x - y))
        nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ d * k) hn]
  rw [gridPriorField, gridPriorField, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hzero j hj),
    abs_mul, abs_of_nonneg hη]
  exact (mul_le_mul_of_nonneg_left hsum hη).trans_eq (by ring)

/-- Interpolation of a uniform oscillation bound and a scale `k` Lipschitz bound. -/
theorem scaled_lipschitz_holder_bound (s b k A r u : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hb : 0 ≤ b) (hk : 0 < k) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hbounded : u ≤ A * (b / k ^ s)) (hlip : u ≤ A * (b / k ^ s) * k * r) :
    u ≤ A * b * r ^ s := by
  have hkp : 0 < k ^ s := Real.rpow_pos_of_pos hk s
  have hrpow : (k * r) ^ s = k ^ s * r ^ s := Real.mul_rpow hk.le hr
  have hcoef : 0 ≤ A * (b / k ^ s) := by positivity
  have heq : A * (b / k ^ s) * (k * r) ^ s = A * b * r ^ s := by
    rw [hrpow]
    field_simp
  by_cases hkr : k * r ≤ 1
  · have hsmall := Real.self_le_rpow_of_le_one (mul_nonneg hk.le hr) hkr hs1
    calc
      u ≤ A * (b / k ^ s) * (k * r) := by nlinarith [hlip]
      _ ≤ A * (b / k ^ s) * (k * r) ^ s := mul_le_mul_of_nonneg_left hsmall hcoef
      _ = _ := heq
  · have hlarge := Real.one_le_rpow (le_of_lt (lt_of_not_ge hkr)) hs
    calc
      u ≤ A * (b / k ^ s) := hbounded
      _ ≤ A * (b / k ^ s) * (k * r) ^ s := by nlinarith
      _ = _ := heq

theorem gridPriorField_holder_bound (d k : ℕ) (s b : ℝ) (hk : 1 ≤ k)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hb : 0 ≤ b)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) (x y : Covariate d) :
    |gridPriorField d k (b / (k : ℝ) ^ s) ξ x - gridPriorField d k (b / (k : ℝ) ^ s) ξ y| ≤
      (68 * (2 : ℝ) ^ d * (d + 1)) * b * euclideanNorm (x - y) ^ s := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hη : 0 ≤ b / (k : ℝ) ^ s := by positivity
  apply scaled_lipschitz_holder_bound s b k (68 * (2 : ℝ) ^ d * (d + 1)) _ _ hs hs1 hb
    hkp (by positivity) (Real.sqrt_nonneg _)
  · have hx := gridPriorField_abs_bound d k _ hη ξ x
    have hy := gridPriorField_abs_bound d k _ hη ξ y
    have hab : |gridPriorField d k (b / (k : ℝ) ^ s) ξ x -
        gridPriorField d k (b / (k : ℝ) ^ s) ξ y| ≤
          |gridPriorField d k (b / (k : ℝ) ^ s) ξ x| + |gridPriorField d k (b / (k : ℝ) ^ s) ξ y| :=
      by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le
          (gridPriorField d k (b / (k : ℝ) ^ s) ξ x) 0 (gridPriorField d k (b / (k : ℝ) ^ s) ξ y))
    nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ d) hη]
  · exact gridPriorField_lipschitz_bound d k _ hη ξ x y

/-- A support patch, defined globally through the same clamp as its window. -/
def gridPatch (d k : ℕ) (j : Fin d → Fin (k + 1)) : Set (Covariate d) :=
  {x | ∀ i, |(k : ℝ) * clampUnit (x i) - (j i).val| ≤ 1}

theorem gridPatch_measurable (d k : ℕ) (j : Fin d → Fin (k + 1)) :
    MeasurableSet (gridPatch d k j) := by
  have heq : gridPatch d k j = ⋂ i : Fin d, {x : Covariate d |
      |(k : ℝ) * clampUnit (x i) - (j i).val| ≤ 1} := by
    ext x
    simp [gridPatch]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le
  · have hc : Continuous (fun x : Covariate d => |(k : ℝ) * clampUnit (x i) - (j i).val|) := by
      unfold clampUnit
      fun_prop
    exact hc.measurable
  · exact measurable_const

theorem gridTensorWindow_zero_outside_patch (d k : ℕ) (j : Fin d → Fin (k + 1))
    (x : Covariate d) (hx : x ∉ gridPatch d k j) : gridTensorWindow d k j x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  have ht : gridTent k (j i) (x i) = 0 := max_eq_left (by linarith [lt_of_not_ge hi])
  exact Finset.prod_eq_zero (Finset.mem_univ i) ((gridWindow_eq_zero_iff k (j i) (x i)).mpr ht)

/-- Actual uniform-design patch probability has the required volume scaling. -/
theorem gridPatch_cube_probability_bound (d k : ℕ) (j : Fin d → Fin (k + 1)) (hk : 0 < k) :
    (cubeVolume d).real (gridPatch d k j) ≤ (2 / (k : ℝ)) ^ d := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  let R : Set (Covariate d) := Set.univ.pi
    (fun i => Icc (((j i).val - 1 : ℝ) / k) (((j i).val + 1 : ℝ) / k))
  have hsub : gridPatch d k j ∩ unitCube d ⊆ R := by
    intro x hx
    rw [Set.mem_pi]
    intro i _
    have hi := hx.1 i
    rw [clampUnit_eq (x i) (hx.2 i)] at hi
    constructor
    · apply (div_le_iff₀ hkp).mpr
      linarith [(abs_le.mp hi).1]
    · apply (le_div_iff₀ hkp).mpr
      linarith [(abs_le.mp hi).2]
  have hvol : volume R = ENNReal.ofReal ((2 / (k : ℝ)) ^ d) := by
    dsimp [R]
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc]
    have hwidth (i : Fin d) : (((j i).val + 1 : ℝ) / k) - (((j i).val - 1 : ℝ) / k) = 2 / k := by ring
    simp_rw [hwidth]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hkp.le) d).symm
  have hbound : cubeVolume d (gridPatch d k j) ≤ ENNReal.ofReal ((2 / (k : ℝ)) ^ d) := by
    rw [cubeVolume, Measure.restrict_apply (gridPatch_measurable d k j), ← hvol]
    exact measure_mono hsub
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

def gridNeighbors (k : ℕ) (j : Fin (k + 1)) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun l => |(j.val : ℝ) - l.val| ≤ 2)

theorem gridNeighbors_card (k : ℕ) (j : Fin (k + 1)) : (gridNeighbors k j).card ≤ 5 := by
  have hsub : (gridNeighbors k j).image Fin.val ⊆ Finset.Icc (j.val - 2) (j.val + 2) := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
    have hdist := (Finset.mem_filter.mp hi).2
    have hl1 : j.val ≤ i.val + 2 := by exact_mod_cast (by linarith [(abs_le.mp hdist).2] :
      (j.val : ℝ) ≤ i.val + 2)
    have hl2 : i.val ≤ j.val + 2 := by exact_mod_cast (by linarith [(abs_le.mp hdist).1] :
      (i.val : ℝ) ≤ j.val + 2)
    exact Finset.mem_Icc.mpr ⟨by omega, hl2⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at h
  omega

def gridTensorNeighbors (d k : ℕ) (j : Fin d → Fin (k + 1)) : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridNeighbors k (j i))

theorem gridTensorNeighbors_card (d k : ℕ) (j : Fin d → Fin (k + 1)) :
    (gridTensorNeighbors d k j).card ≤ 5 ^ d := by
  rw [gridTensorNeighbors, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 5 := Finset.prod_le_prod (fun i _ => gridNeighbors_card k (j i))
    _ = _ := by simp

theorem gridPatch_common_point_neighbors (d k : ℕ) (j l : Fin d → Fin (k + 1))
    (x : Covariate d) (hj : x ∈ gridPatch d k j) (hl : x ∈ gridPatch d k l) :
    l ∈ gridTensorNeighbors d k j := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hj' := abs_le.mp (hj i)
  have hl' := abs_le.mp (hl i)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every actual observation-support graph has uniformly bounded closed degree. -/
theorem grid_observed_patch_degree (d k n : ℕ) (x : Fin n → Covariate d)
    (j : Fin d → Fin (k + 1)) :
    (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l)).card ≤ 5 ^ d := by
  have hsub : (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l)) ⊆ gridTensorNeighbors d k j := by
    intro l hl
    obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hl).2
    exact gridPatch_common_point_neighbors d k j l (x i) (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hi').2
  exact (Finset.card_le_card hsub).trans (gridTensorNeighbors_card d k j)

/-- Every latent grid state lies in the original model, for all extension
domains U, with the variance path separated by exactly eta squared. -/
theorem grid_prior_state_admissible {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (b t : ℝ)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) (hk : 1 ≤ k)
    (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : (2 : ℝ) ^ d * b ≤ P.ρ) (hvariance : b ^ 2 ≤ P.ρ)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound) :
    ∃ θ : RegressionParameter d, Admissible C θ ∧
      θ.regression = gridPriorField d k (b / (k : ℝ) ^ C.smoothness) ξ ∧
      θ.variance = P.variancePath (b / (k : ℝ) ^ C.smoothness) t := by
  let η := b / (k : ℝ) ^ C.smoothness
  let F := gridPriorField d k η ξ
  have hkp : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hpower : 1 ≤ (k : ℝ) ^ C.smoothness := Real.one_le_rpow (by exact_mod_cast hk) C.smoothness_pos.le
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηb : η ≤ b := div_le_self hb hpower
  have hηρ : η ^ 2 ≤ P.ρ := (by nlinarith [hηb] : η ^ 2 ≤ b ^ 2).trans hvariance
  have hsup (x : Covariate d) : |F x| ≤ (2 : ℝ) ^ d * b :=
    (gridPriorField_abs_bound d k η hη ξ x).trans (mul_le_mul_of_nonneg_left hηb (by positivity))
  have hlegal (x : Covariate d) := P.path_legality η t (F x) ht hηρ ((hsup x).trans hfield)
  have hp : ∀ x y, 0 ≤ ternaryMass P.a (F x) (P.variancePath η t) y :=
    fun x y => P.c_pos.le.trans ((hlegal x).2.2.1 y)
  have hF : Continuous F := gridPriorField_continuous d k η ξ
  let θ := uniformTernaryParameter P.a (P.variancePath η t) F hF.measurable P.a_pos.ne' hp
  have horder : C.order = 0 := by
    have ho : (C.order : ℝ) < 1 := C.order_lt.trans_le hs1
    have hnat : C.order < 1 := by exact_mod_cast ho
    omega
  refine ⟨θ, ?_, rfl, rfl⟩
  apply uniformTernaryParameter_admissible_order_zero C P.a (P.variancePath η t) F hF horder P.a_pos.ne' hp
    (hlegal 0).1.le (hlegal 0).2.1.le ((2 : ℝ) ^ d * b)
    ((68 * (2 : ℝ) ^ d * (d + 1)) * b) (by positivity) (by positivity)
    (by nlinarith [hholder]) hsup
  · exact gridPriorField_holder_bound d k C.smoothness b hk C.smoothness_pos.le hs1 hb ξ
  · intro x
    have hf := (hlegal x).2.2.2
    rw [ternary_fourth_central_moment P.a (F x) (P.variancePath η t) P.a_pos.ne'] at hf
    exact hf

end NearlyMinimax
