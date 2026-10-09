module

public import NearlyMinimax.PilotFeatures
public import NearlyMinimax.AnchoredExpansion
public import NearlyMinimax.PairWindowGeometry


@[expose] public section

/-! The manuscript's actual raw current-cell pilot coordinates and their
original-law second-moment budget, allowing unbounded responses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev LocalPilotIndex (d ℓ : ℕ) :=
  Sum (AnchoredIndex d ℓ × AnchoredIndex d ℓ) (Sum (AnchoredIndex d ℓ) (AnchoredIndex d ℓ))

def dyadicPilotScale (d j : ℕ) : ℝ := ((2 : ℝ) ^ j) ^ d

theorem dyadicPilotScale_pos (d j : ℕ) : 0 < dyadicPilotScale d j := by
  unfold dyadicPilotScale
  positivity

def dyadicPilotCell {d : ℕ} (j : ℕ) (x : Covariate d) : Set (Covariate d) :=
  {z | regularGridCell ((2 : ℕ) ^ j) (by positivity) z =
    regularGridCell ((2 : ℕ) ^ j) (by positivity) x}

theorem dyadicPilotCell_measurable {d : ℕ} (j : ℕ) (x : Covariate d) :
    MeasurableSet (dyadicPilotCell j x) :=
  measurableSet_eq_fun (regular_grid_cell_measurable _ _) measurable_const

theorem dyadicAnchoredFeature_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : Measurable (fun z => dyadicAnchoredFeature j x z γ) := by
  exact ((anchoredMonomial_continuous γ).comp (continuous_pi (fun i =>
    continuous_const.mul ((continuous_apply i).sub continuous_const)))).measurable

/-- Current-cell normalization bounds the exact anchored monomials, including
the assigned right cube boundary. -/
theorem dyadicAnchoredFeature_abs_le_one {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell j x)
    (γ : AnchoredIndex d ℓ) : |dyadicAnchoredFeature j x z γ| ≤ 1 := by
  apply anchoredMonomial_abs_le_one
  intro i
  have hr := regular_grid_same_cell_radius ((2 : ℕ) ^ j) (by positivity) z x hz hx hc i
  have hk : 0 < (2 : ℝ) ^ j := by positivity
  have he : (((2 : ℕ) ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by simp
  rw [he] at hr
  rw [abs_mul, abs_of_pos hk]
  exact (mul_le_mul_of_nonneg_left hr hk.le).trans_eq (by field_simp)

def dyadicPilotScalar {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  match a with
  | Sum.inl (γ, δ) => dyadicAnchoredFeature j x z.1 γ * dyadicAnchoredFeature j x z.1 δ
  | Sum.inr (Sum.inl γ) => z.2 * dyadicAnchoredFeature j x z.1 γ
  | Sum.inr (Sum.inr γ) => dyadicAnchoredFeature j x z.1 γ

/-- The actual raw coordinates: normalized Gram, response vector, and
constant-response vector. Their mean is taken under the original law. -/
def dyadicPilotFeature {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  dyadicPilotScale d j * (Prod.fst ⁻¹' dyadicPilotCell j x).indicator
    (dyadicPilotScalar j x a) z

theorem dyadicPilotScalar_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : Measurable (dyadicPilotScalar j x a) := by
  cases a with
  | inl a =>
    exact ((dyadicAnchoredFeature_measurable j x a.1).comp measurable_fst).mul
      ((dyadicAnchoredFeature_measurable j x a.2).comp measurable_fst)
  | inr a =>
    cases a with
    | inl γ =>
      exact measurable_snd.mul
        ((dyadicAnchoredFeature_measurable j x γ).comp measurable_fst)
    | inr γ => exact (dyadicAnchoredFeature_measurable j x γ).comp measurable_fst

theorem dyadicPilotFeature_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : Measurable (dyadicPilotFeature j x a) :=
  measurable_const.mul ((dyadicPilotScalar_measurable j x a).indicator
    (measurable_fst (dyadicPilotCell_measurable j x)))

theorem dyadicPilotScalar_abs_bound {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) (hx : x ∈ unitCube d)
    (hz : z.1 ∈ unitCube d) (hc : z.1 ∈ dyadicPilotCell j x) :
    |dyadicPilotScalar j x a z| ≤ 1 + |z.2| := by
  have hb := dyadicAnchoredFeature_abs_le_one (ℓ := ℓ) j x z.1 hx hz hc
  cases a with
  | inl a =>
    change |dyadicAnchoredFeature j x z.1 a.1 * dyadicAnchoredFeature j x z.1 a.2| ≤ _
    rw [abs_mul]
    apply (mul_le_mul (hb a.1) (hb a.2) (abs_nonneg _) (by norm_num)).trans
    simp only [one_mul]
    exact le_add_of_nonneg_right (abs_nonneg z.2)
  | inr a =>
    cases a with
    | inl γ =>
      change |z.2 * dyadicAnchoredFeature j x z.1 γ| ≤ _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hb γ) (abs_nonneg z.2)).trans (by linarith)
    | inr γ => exact (hb γ).trans (le_add_of_nonneg_right (abs_nonneg z.2))

/-- Exact geometric support and the paper's raw feature envelope. -/
theorem dyadicPilotFeature_abs_bound {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) (hx : x ∈ unitCube d)
    (hz : z.1 ∈ unitCube d) :
    |dyadicPilotFeature j x a z| ≤ dyadicPilotScale d j *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator
        (fun z : Observation d => 1 + |z.2|) z := by
  by_cases hc : z.1 ∈ dyadicPilotCell j x
  · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
    simp only [dyadicPilotFeature, indicator_of_mem hc', abs_mul,
      abs_of_pos (dyadicPilotScale_pos d j)]
    exact mul_le_mul_of_nonneg_left (dyadicPilotScalar_abs_bound j x a z hx hz hc)
      (dyadicPilotScale_pos d j).le
  · simp [dyadicPilotFeature, hc]

theorem dyadicPilotFeature_memLp_two {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    MemLp (dyadicPilotFeature j x a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hd : MemLp (fun z : Observation d => dyadicPilotScale d j * (1 + |z.2|))
      2 (observationLaw θ) := ((memLp_const (1 : ℝ)).add hy).const_mul _
  apply hd.mono' (dyadicPilotFeature_measurable j x a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  rw [Real.norm_eq_abs]
  apply (dyadicPilotFeature_abs_bound j x a z hx hz).trans
  by_cases hc : z.1 ∈ dyadicPilotCell j x <;> simp [hc]
  exact mul_nonneg (dyadicPilotScale_pos d j).le (by positivity)

def dyadicPilotMomentConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 * (1 + responseSecondBound C)) * C.densityUpper

theorem dyadicPilotMomentConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < dyadicPilotMomentConstant C := by
  have hden := C.one_lt_densityUpper
  have hresp := responseSecondBound_pos C
  unfold dyadicPilotMomentConstant
  positivity

/-- The order-independent raw coordinate budget `C_g K_j` follows from
the actual cell volume, design density cap, and conditional error moment. -/
theorem dyadicPilotFeature_second_le {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hd : Integrable (fun z : Observation d => dyadicPilotScale d j ^ 2 *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator (fun z : Observation d => (1 + |z.2|) ^ 2) z)
      (observationLaw θ) :=
    (((memLp_const (1 : ℝ)).add hy).integrable_sq.indicator
      (measurable_fst (dyadicPilotCell_measurable j x))).const_mul _
  have hfirst : (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotScale d j ^ 2 *
        ((2 * (1 + responseSecondBound C)) * (designLaw θ).real (dyadicPilotCell j x)) := by
    apply (integral_mono_ae (dyadicPilotFeature_memLp_two C θ hθ j x hx a).integrable_sq hd ?_).trans
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (observationLaw_localized_response_energy_le C θ hθ _
        (dyadicPilotCell_measurable j x)) (sq_nonneg _)
    · filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
      have hb := dyadicPilotFeature_abs_bound j x a z hx hz
      by_cases hc : z.1 ∈ dyadicPilotCell j x
      · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
        simp only [indicator_of_mem hc'] at hb ⊢
        change dyadicPilotFeature j x a z ^ 2 ≤ dyadicPilotScale d j ^ 2 * (1 + |z.2|) ^ 2
        simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      · simp [dyadicPilotFeature, hc]
  have hmass : (designLaw θ).real (dyadicPilotCell j x) ≤ C.densityUpper / dyadicPilotScale d j := by
    convert regularGridProbability_cap C θ hθ ((2 : ℕ) ^ j) (by positivity)
      (regularGridCell ((2 : ℕ) ^ j) (by positivity) x) using 1 <;>
      simp only [dyadicPilotCell, regularGridProbability, Set.preimage, Set.mem_singleton_iff,
        dyadicPilotScale, Nat.cast_pow, Nat.cast_ofNat]
  apply hfirst.trans
  have hfactor : 0 ≤ dyadicPilotScale d j ^ 2 * (2 * (1 + responseSecondBound C)) := by
    have := responseSecondBound_pos C
    positivity
  have hm := mul_le_mul_of_nonneg_left hmass hfactor
  have heq : dyadicPilotScale d j ^ 2 * (2 * (1 + responseSecondBound C)) *
      (C.densityUpper / dyadicPilotScale d j) =
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    unfold dyadicPilotMomentConstant
    field_simp [ne_of_gt (dyadicPilotScale_pos d j)] <;> ring
  rw [heq] at hm
  simpa only [mul_assoc] using hm

/-- The full vector second moment has only the fixed local feature dimension
as an additional factor. -/
theorem dyadicPilotFeature_vector_energy_le {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    (∫ z, ∑ a : LocalPilotIndex d ℓ, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      Fintype.card (LocalPilotIndex d ℓ) * dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  rw [integral_finsetSum _ (fun a _ => (dyadicPilotFeature_memLp_two C θ hθ j x hx a).integrable_sq)]
  exact (Finset.sum_le_sum (fun a _ => dyadicPilotFeature_second_le C θ hθ j x hx a)).trans_eq
    (by simp [mul_assoc])

def dyadicPilotPopulation {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    LocalPilotIndex d ℓ → ℝ := fun a => ∫ z, dyadicPilotFeature j x a z ∂observationLaw θ

end NearlyMinimax
