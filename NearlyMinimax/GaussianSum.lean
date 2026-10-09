module

public import Mathlib


@[expose] public section

/-!
# Uniform Gaussian sums over separated sets and arithmetic lattices

The separated-set and integral-comparison proofs below are adapted from the
companion formalization's `RoughRegime/Separated.lean` and
`RoughRegime/Window.lean`. They are checked here against Lean 4.24.0.
The lattice consequence supplies the Gaussian sum step in `upper_E.tex`,
`eq:U12-term`, with a constant independent of the center and number of terms.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace NearlyMinimax.GaussianSum

/-- The kth point of a nonnegative δ-separated finite set lies at least kδ from zero. -/
theorem orderEmbOfFin_ge_mul_sep (S : Finset ℝ) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|)
    (k : Fin S.card) : (k.val : ℝ) * δ ≤ S.orderEmbOfFin rfl k := by
  have hrank : ∀ (n : ℕ) (hn : n < S.card),
      (n : ℝ) * δ ≤ S.orderEmbOfFin rfl ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      simpa using hnonneg _ (S.orderEmbOfFin_mem rfl ⟨0, hn⟩)
    | succ n ih =>
      intro hn
      have hn' : n < S.card := Nat.lt_trans (Nat.lt_succ_self n) hn
      have hlt : S.orderEmbOfFin rfl ⟨n, hn'⟩ <
          S.orderEmbOfFin rfl ⟨n + 1, hn⟩ :=
        (S.orderEmbOfFin rfl).strictMono (by simp)
      have hstep := hsep _ (S.orderEmbOfFin_mem rfl ⟨n + 1, hn⟩)
        _ (S.orderEmbOfFin_mem rfl ⟨n, hn'⟩) (ne_of_gt hlt)
      rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at hstep
      have hi := ih hn'
      push_cast
      linarith
  exact hrank k.val k.isLt

/-- A separated finite Gaussian sum is bounded by its equally spaced comparison sum. -/
theorem separated_gaussian_sum_le (S : Finset ℝ) {δ c : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ∑ x ∈ S, Real.exp (-c * x ^ 2) ≤
      ∑ k ∈ Finset.range S.card, Real.exp (-(c * δ ^ 2) * (k : ℝ) ^ 2) := by
  have hsum : ∑ x ∈ S, Real.exp (-c * x ^ 2) =
      ∑ k : Fin S.card, Real.exp (-c * (S.orderEmbOfFin rfl k) ^ 2) := by
    simpa only [Finset.sum_map, RelEmbedding.coe_toEmbedding] using
      congrArg (fun t : Finset ℝ => ∑ x ∈ t, Real.exp (-c * x ^ 2))
        (S.map_orderEmbOfFin_univ (k := S.card) rfl).symm
  rw [hsum]
  calc
    (∑ k : Fin S.card, Real.exp (-c * (S.orderEmbOfFin rfl k) ^ 2)) ≤
        ∑ k : Fin S.card, Real.exp (-(c * δ ^ 2) * (k.val : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      apply Real.exp_le_exp.mpr
      have hn := hnonneg _ (S.orderEmbOfFin_mem rfl k)
      have hk := orderEmbOfFin_ge_mul_sep S hδ.le hnonneg hsep k
      have hp : 0 ≤ (k.val : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      have hs := (sq_le_sq₀ hp hn).mpr hk
      nlinarith
    _ = ∑ k ∈ Finset.range S.card, Real.exp (-(c * δ ^ 2) * (k : ℝ) ^ 2) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range.mp hk]

/-- A Gaussian is decreasing on the nonnegative half-line. -/
theorem gaussian_antitone {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Ici 0) := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hs : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).2 hxy
  nlinarith [mul_le_mul_of_nonneg_left hs hc]

/-- The elementary Gaussian partial-sum bound used in the window estimate. -/
theorem gaussian_sum_range_le (c : ℝ) (hc : 0 < c) (N : ℕ) :
    (∑ k ∈ Finset.range N, Real.exp (-c * (k : ℝ) ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / 2 := by
  cases N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ N =>
      rw [Finset.sum_range_succ']
      have hf : AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2))
          (Icc 0 (0 + (N : ℝ))) := by
        simpa using (gaussian_antitone hc.le).mono (Icc_subset_Ici_self :
          Icc (0 : ℝ) (N : ℝ) ⊆ Ici 0)
      have hcomp' := hf.sum_le_integral
      have hInt : (∫ x in (0 : ℝ)..(N : ℝ), Real.exp (-c * x ^ 2)) ≤
          (∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2)) := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
        apply setIntegral_mono_set (integrable_exp_neg_mul_sq hc).integrableOn
          (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
        exact Filter.Eventually.of_forall fun x hx => hx.1
      have hcomp : (∑ k ∈ Finset.range N,
          Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) ≤
          (∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2)) := by
        simpa using (by simpa using hcomp' :
          (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) ≤
            (∫ x in (0 : ℝ)..(N : ℝ), Real.exp (-c * x ^ 2))).trans hInt
      calc
        (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) +
            Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2)
          ≤ (∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2)) + 1 := by
              simpa using add_le_add_right hcomp 1
        _ = 1 + Real.sqrt (Real.pi / c) / 2 := by
              rw [integral_gaussian_Ioi]
              ring

/-- Rewriting the Gaussian constant for a positive lattice spacing. -/
theorem gaussian_constant_spacing (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    Real.sqrt (Real.pi / (c * δ ^ 2)) = Real.sqrt (Real.pi / c) / δ := by
  have halg : Real.pi / (c * δ ^ 2) = (Real.pi / c) / δ ^ 2 := by
    field_simp
  rw [halg, Real.sqrt_div (div_nonneg Real.pi_pos.le hc.le),
    Real.sqrt_sq_eq_abs, abs_of_pos hδ]

/-- Translating a separated finite set preserves its separation. -/
theorem separated_translate (S : Finset ℝ) (δ a : ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ∀ u ∈ S.image (fun x => x - a), ∀ v ∈ S.image (fun x => x - a),
      u ≠ v → δ ≤ |u - v| := by
  classical
  intro u hu v hv huv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  have hxy : x ≠ y := by
    intro h
    exact huv (congrArg (fun z => z - a) h)
  have h := hsep x hx y hy hxy
  convert h using 1
  congr 1
  ring

/-- Reflection about a center preserves separation. -/
theorem separated_reflect (S : Finset ℝ) (δ a : ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ∀ u ∈ S.image (fun x => a - x), ∀ v ∈ S.image (fun x => a - x),
      u ≠ v → δ ≤ |u - v| := by
  classical
  intro u hu v hv huv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  have hxy : x ≠ y := by
    intro h
    exact huv (congrArg (fun z => a - z) h)
  have h := hsep x hx y hy hxy
  rw [abs_sub_comm x y] at h
  convert h using 1
  congr 1
  ring

/-- A nonnegative separated Gaussian sum is bounded by the half Gaussian integral. -/
theorem gaussian_half_sum (S : Finset ℝ) {δ c : ℝ}
    (hδ : 0 < δ) (hc : 0 < c)
    (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, Real.exp (-c * x ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / δ / 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range S.card,
          Real.exp (-(c * δ ^ 2) * (k : ℝ) ^ 2) :=
        separated_gaussian_sum_le S hδ hc hnonneg hsep
    _ ≤ 1 + Real.sqrt (Real.pi / (c * δ ^ 2)) / 2 :=
        gaussian_sum_range_le (c * δ ^ 2) (by positivity) S.card
    _ = 1 + Real.sqrt (Real.pi / c) / δ / 2 := by
        rw [gaussian_constant_spacing c δ hc hδ]

/-- A Gaussian sum over an arbitrary separated finite set, centered at a. -/
theorem gaussian_centered_sum (S : Finset ℝ) {δ c : ℝ} (a : ℝ)
    (hδ : 0 < δ) (hc : 0 < c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, Real.exp (-c * (x - a) ^ 2)) ≤
      2 + Real.sqrt (Real.pi / c) / δ := by
  classical
  let P := S.filter (fun x => a ≤ x)
  let N := S.filter (fun x => ¬a ≤ x)
  have hPsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hNsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hPnonneg : ∀ u ∈ P.image (fun x => x - a), 0 ≤ u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact sub_nonneg.mpr (Finset.mem_filter.mp hx).2
  have hNnonneg : ∀ u ∈ N.image (fun x => a - x), 0 ≤ u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact sub_nonneg.mpr (not_le.mp (Finset.mem_filter.mp hx).2).le
  have hP := gaussian_half_sum (P.image (fun x => x - a)) hδ hc hPnonneg
    (separated_translate P δ a hPsep)
  have hN := gaussian_half_sum (N.image (fun x => a - x)) hδ hc hNnonneg
    (separated_reflect N δ a hNsep)
  rw [Finset.sum_image (by intro x hx y hy h; linarith)] at hP
  rw [Finset.sum_image (by intro x hx y hy h; linarith)] at hN
  have hN' : (∑ x ∈ N, Real.exp (-c * (x - a) ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / δ / 2 := by
    convert hN using 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ring
  have hsplit : (∑ x ∈ S, Real.exp (-c * (x - a) ^ 2)) =
      (∑ x ∈ P, Real.exp (-c * (x - a) ^ 2)) +
      (∑ x ∈ N, Real.exp (-c * (x - a) ^ 2)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun x => a ≤ x)
      (fun x => Real.exp (-c * (x - a) ^ 2))).symm
  rw [hsplit]
  linarith


/-- An arithmetic lattice has separation equal to its positive step. -/
theorem arithmetic_lattice_separated (u₀ b : ℝ) (hb : 0 < b) (A : Finset ℕ) :
    ∀ x ∈ A.image (fun j : ℕ => u₀ + (j : ℝ) * b),
      ∀ y ∈ A.image (fun j : ℕ => u₀ + (j : ℝ) * b),
        x ≠ y → b ≤ |x - y| := by
  classical
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  have hij : i ≠ j := by intro he; apply hxy; rw [he]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have hdiff : b ≤ (u₀ + (j : ℝ) * b) - (u₀ + (i : ℝ) * b) := by nlinarith
    exact hdiff.trans (le_abs_self _ |>.trans_eq (abs_sub_comm _ _))
  · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have hdiff : b ≤ (u₀ + (i : ℝ) * b) - (u₀ + (j : ℝ) * b) := by nlinarith
    exact hdiff.trans (le_abs_self _)

/-- A finite lattice Gaussian sum with an explicit bound uniform in its center. -/
theorem gaussian_lattice_sum_le (A : Finset ℕ) (u₀ a b S : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hS : 1 ≤ S) :
    (∑ j ∈ A, Real.exp (-a * (u₀ + (j : ℝ) * b) ^ 2 / S)) ≤
      (2 + Real.sqrt (Real.pi / a) / b) * Real.sqrt S := by
  classical
  have hS₀ : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hgauss := gaussian_centered_sum
    (A.image (fun j : ℕ => u₀ + (j : ℝ) * b)) (0 : ℝ) hb (div_pos ha hS₀)
    (arithmetic_lattice_separated u₀ b hb A)
  have hinj : Set.InjOn (fun j : ℕ => u₀ + (j : ℝ) * b) A := by
    intro i hi j hj he
    have hcast : (i : ℝ) = (j : ℝ) := by nlinarith
    exact_mod_cast hcast
  rw [Finset.sum_image hinj] at hgauss
  simp only [sub_zero] at hgauss
  have hsum : (∑ j ∈ A, Real.exp (-a * (u₀ + (j : ℝ) * b) ^ 2 / S)) =
      ∑ j ∈ A, Real.exp (-(a / S) * (u₀ + (j : ℝ) * b) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring
  rw [hsum]
  have halg : Real.pi / (a / S) = Real.pi / a * S := by field_simp
  rw [halg, Real.sqrt_mul (div_nonneg Real.pi_pos.le ha.le)] at hgauss
  have hsqrt : 1 ≤ Real.sqrt S := Real.one_le_sqrt.2 hS
  calc
    _ ≤ 2 + Real.sqrt (Real.pi / a) * Real.sqrt S / b := hgauss
    _ ≤ (2 + Real.sqrt (Real.pi / a) / b) * Real.sqrt S := by
      rw [show Real.sqrt (Real.pi / a) * Real.sqrt S / b =
        (Real.sqrt (Real.pi / a) / b) * Real.sqrt S by ring]
      nlinarith

/-- The consecutive-index form used in the allocation proof in `upper_E.tex`. -/
theorem gaussian_sum_range_sqrt_bound (N : ℕ) (u₀ a b S : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hS : 1 ≤ S) :
    (∑ j ∈ Finset.range N, Real.exp (-a * (u₀ + (j : ℝ) * b) ^ 2 / S)) ≤
      (2 + Real.sqrt (Real.pi / a) / b) * Real.sqrt S :=
  gaussian_lattice_sum_le (Finset.range N) u₀ a b S ha hb hS

/-- After the `S⁻¹ᐟ²` factor in `eq:U12-term`, the allocation sum is uniformly bounded. -/
theorem normalized_gaussian_lattice_sum_le (A : Finset ℕ) (u₀ a b S : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hS : 1 ≤ S) :
    (∑ j ∈ A, Real.exp (-a * (u₀ + (j : ℝ) * b) ^ 2 / S)) / Real.sqrt S ≤
      2 + Real.sqrt (Real.pi / a) / b := by
  have hp : 0 < Real.sqrt S := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hS)
  exact (div_le_iff₀ hp).2 (gaussian_lattice_sum_le A u₀ a b S ha hb hS)

end NearlyMinimax.GaussianSum
