module

public import NearlyMinimax.Allocation
public import NearlyMinimax.SaddleAsymptotics


@[expose] public section

/-!
# Uniform scalar bounds for the floored allocation degrees

These lemmas prove the `O(log(n)^(3/2))` maximum-degree bound in the upper
allocation, from the explicit width and the actual scalar level-range bounds.
The ensuing sample-size comparison is uniform in the number of levels.
-/

noncomputable section
open Filter
open scoped Topology

namespace NearlyMinimax

theorem sq_div_sqrt_eq_mul_sqrt {L : ℝ} (hL : 0 < L) :
    L ^ 2 / Real.sqrt L = L * Real.sqrt L := by
  apply (div_eq_iff (Real.sqrt_pos.2 hL).ne').2
  rw [mul_assoc, Real.mul_self_sqrt hL.le]
  ring

theorem mul_sqrt_eq_three_halves_power {L : ℝ} (hL : 0 < L) :
    L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
  calc
    L * Real.sqrt L = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = L ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hL 1 (1 / 2)).symm
    _ = L ^ (3 / 2 : ℝ) := by norm_num

/-- A uniform profile bound throughout all coarse and fine levels. -/
theorem quadraticProfile_degree_scale_bound {L S z c C : ℝ}
    (hL : 1 ≤ L) (hc : 0 < c) (hC : 0 ≤ C)
    (hSl : c * Real.sqrt L ≤ S) (hSu : S ≤ C * Real.sqrt L)
    (hzl : -L ≤ z) (hzu : z ≤ S) :
    quadraticProfile S z ≤ (C / 4 + (C + 1) ^ 2 / c) * L ^ (3 / 2 : ℝ) := by
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL₀
  have hdenom : 0 < c * Real.sqrt L := mul_pos hc hsqrt
  have hS : 0 < S := hdenom.trans_le hSl
  have hsqrtL : Real.sqrt L ≤ L := (Real.sqrt_le_left hL₀.le).2 (by nlinarith)
  have hSC : S ≤ C * L := hSu.trans (mul_le_mul_of_nonneg_left hsqrtL hC)
  have hdiff : 0 ≤ S - z := sub_nonneg.2 hzu
  have hdiffup : S - z ≤ (C + 1) * L := by nlinarith
  have hboundpos : 0 ≤ (C + 1) * L := by positivity
  have hsq : (S - z) ^ 2 ≤ ((C + 1) * L) ^ 2 := (sq_le_sq₀ hdiff hboundpos).2 hdiffup
  have hterm : (S - z) ^ 2 / S ≤ ((C + 1) ^ 2 / c) * (L * Real.sqrt L) := by
    calc
      _ ≤ (S - z) ^ 2 / (c * Real.sqrt L) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenom hSl
      _ ≤ ((C + 1) * L) ^ 2 / (c * Real.sqrt L) :=
        div_le_div_of_nonneg_right hsq hdenom.le
      _ = ((C + 1) ^ 2 / c) * (L ^ 2 / Real.sqrt L) := by ring
      _ = _ := by rw [sq_div_sqrt_eq_mul_sqrt hL₀]
  have hfirst : S / 4 ≤ (C / 4) * (L * Real.sqrt L) := by
    have hm := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ C * Real.sqrt L / 4)
    have hs := div_le_div_of_nonneg_right hSu (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  unfold quadraticProfile
  rw [← mul_sqrt_eq_three_halves_power hL₀]
  nlinarith

/-- The actual width is eventually between fixed positive square-root multiples. -/
theorem eventually_allocationWidth_comparable {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      (a / 2) * Real.sqrt (Real.log x) ≤ allocationWidth a C x ∧
        allocationWidth a C x ≤ (2 * a) * Real.sqrt (Real.log x) := by
  have ht := allocationWidth_div_sqrt_log_limit a C
  filter_upwards [ht.eventually (lt_mem_nhds (by linarith : a / 2 < a)),
    ht.eventually (gt_mem_nhds (by linarith : a < 2 * a)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hlo hhi hx
  have hp : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hx)
  exact ⟨hx, ((lt_div_iff₀ hp).1 hlo).le, ((div_lt_iff₀ hp).1 hhi).le⟩

/-- The explicit coefficient of the uniform maximum-degree bound. -/
def allocationDegreeCoefficient (a β : ℝ) : ℝ :=
  β * ((2 * a) / 4 + (2 * a + 1) ^ 2 / (a / 2))

/-- Uniformly over any family of finite level sets, the actual degrees have the claimed scale. -/
theorem eventually_allocation_degree_bound {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β)
    (C : ℝ) (A : ℝ → Finset ℕ) (z : ℝ → ℕ → ℝ)
    (hrange : ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
      -Real.log x ≤ z x j ∧ z x j ≤ allocationWidth a C x) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
      (Nat.floor (β * quadraticProfile (allocationWidth a C x) (z x j)) : ℝ) ≤
        allocationDegreeCoefficient a β * (Real.log x) ^ (3 / 2 : ℝ) := by
  filter_upwards [eventually_allocationWidth_comparable ha C, hrange] with x hx hz
  intro j hj
  have hp := quadraticProfile_degree_scale_bound hx.1 (by positivity : 0 < a / 2)
    (by positivity : 0 ≤ 2 * a) hx.2.1 hx.2.2 (hz j hj).1 (hz j hj).2
  have hS : 0 < allocationWidth a C x :=
    (mul_pos (by positivity : 0 < a / 2) (Real.sqrt_pos.2 (by linarith : 0 < Real.log x))).trans_le hx.2.1
  have hQ : 0 ≤ quadraticProfile (allocationWidth a C x) (z x j) :=
    (by positivity : (0 : ℝ) ≤ allocationWidth a C x / 4).trans (quadraticProfile_lower hS)
  have hf := Nat.floor_le (mul_nonneg hβ hQ)
  have hm := mul_le_mul_of_nonneg_left hp hβ
  unfold allocationDegreeCoefficient
  exact hf.trans (by simpa only [mul_assoc] using hm)

/-- All degrees are eventually smaller than any fixed sample fraction. -/
theorem eventually_allocation_degree_lt_sample_fraction {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β)
    (C : ℝ) (A : ℝ → Finset ℕ) (z : ℝ → ℕ → ℝ)
    (hrange : ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
      -Real.log x ≤ z x j ∧ z x j ≤ allocationWidth a C x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
      (Nat.floor (β * quadraticProfile (allocationWidth a C x) (z x j)) : ℝ) < δ * x := by
  filter_upwards [eventually_allocation_degree_bound ha hβ C A z hrange,
    eventually_log_power_lt_sample (3 / 2) (allocationDegreeCoefficient a β) hδ] with x hx hs
  intro j hj
  exact (hx j hj).trans_lt hs

/-- The actual natural terminal level before spatial bandwidth rounding. -/
def terminalAllocationLevel (δ a C H γ x : ℝ) : ℕ :=
  Nat.floor ((Real.log x + candidateTerminalDepth a C H γ x) / δ)

/-- The actual shifted logarithmic position of a dyadic level. -/
def allocationLevelPosition (δ a C H x : ℝ) (j : ℕ) : ℝ :=
  δ * (j : ℝ) - Real.log x + Real.log (H * allocationWidth a C x)

/-- The level-range bound follows directly from terminal flooring and the logarithmic correction. -/
theorem actual_allocation_level_range {δ a C H γ x : ℝ} {j : ℕ}
    (hδ : 0 < δ) (hγ : 0 ≤ γ) (hS : 1 ≤ allocationWidth a C x)
    (hHS : 1 ≤ H * allocationWidth a C x)
    (hLT : 0 ≤ Real.log x + candidateTerminalDepth a C H γ x)
    (hj : j ≤ terminalAllocationLevel δ a C H γ x) :
    -Real.log x ≤ allocationLevelPosition δ a C H x j ∧
      allocationLevelPosition δ a C H x j ≤ allocationWidth a C x := by
  have hell : 0 ≤ Real.log (H * allocationWidth a C x) := Real.log_nonneg hHS
  have hlogS : 0 ≤ Real.log (allocationWidth a C x) := Real.log_nonneg hS
  have hjreal : (j : ℝ) ≤ (terminalAllocationLevel δ a C H γ x : ℝ) := by exact_mod_cast hj
  have hf := Nat.floor_le (div_nonneg hLT hδ.le)
  have hum := mul_le_mul_of_nonneg_left hf hδ.le
  have hmj := mul_le_mul_of_nonneg_left hjreal hδ.le
  have he : δ * ((Real.log x + candidateTerminalDepth a C H γ x) / δ) =
      Real.log x + candidateTerminalDepth a C H γ x := by field_simp
  rw [he] at hum
  unfold terminalAllocationLevel at hmj
  unfold allocationLevelPosition
  constructor
  · linarith [mul_nonneg hδ.le (Nat.cast_nonneg j)]
  · unfold candidateTerminalDepth at hum hmj
    linarith [mul_nonneg hγ hlogS]

/-- All actual dyadic level positions eventually satisfy the uniform profile range. -/
theorem eventually_actual_allocation_level_range {δ a H γ : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hH : 0 < H) (hγ : 0 ≤ γ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (terminalAllocationLevel δ a C H γ x + 1),
      -Real.log x ≤ allocationLevelPosition δ a C H x j ∧
        allocationLevelPosition δ a C H x j ≤ allocationWidth a C x := by
  have hw := allocationWidth_tendsto_atTop ha C
  have hHw := hw.const_mul_atTop hH
  filter_upwards [hw.eventually (eventually_ge_atTop (1 : ℝ)),
    hHw.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_terminal_cell_log_nonneg ha hH C γ] with x hx hHx hLT
  intro j hj
  exact actual_allocation_level_range hδ hγ hx hHx hLT (by
    have hmem := Finset.mem_range.1 hj
    omega)

/-- The explicit dyadic allocation meets every fixed degree-to-sample-size guard eventually. -/
theorem eventually_actual_allocation_degree_lt_sample_fraction {δ a H β γ : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hH : 0 < H) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (terminalAllocationLevel δ a C H γ x + 1),
      (Nat.floor (β * quadraticProfile (allocationWidth a C x)
        (allocationLevelPosition δ a C H x j)) : ℝ) < ε * x :=
  eventually_allocation_degree_lt_sample_fraction ha hβ C
    (fun x => Finset.range (terminalAllocationLevel δ a C H γ x + 1))
    (allocationLevelPosition δ a C H)
    (eventually_actual_allocation_level_range hδ ha hH hγ C) hε

end NearlyMinimax
