module

public import NearlyMinimax.FinitePartitionMoments
public import NearlyMinimax.ObservationMoments
public import NearlyMinimax.PairUStatistic


@[expose] public section

/-! Fourth-moment and row-localization estimates for the actual same-cell
pair-difference score. Responses are allowed to be unbounded. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Partition
variable {X B : Type*} [MeasurableSpace X] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableEq B]
  (μ : Measure X) [IsProbabilityMeasure μ] (label : X → B) (hlabel : Measurable label)
include hlabel

def labelLocalizedKernel (g : X → ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then g z.2 else 0

theorem labelLocalizedKernel_measurable (g : X → ℝ) (hg : Measurable g) :
    Measurable (labelLocalizedKernel label g) := by
  unfold labelLocalizedKernel
  exact Measurable.ite
    (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
    (hg.comp measurable_snd) measurable_const

theorem labelLocalizedKernel_integrable (g : X → ℝ) (hg : Integrable g μ) :
    Integrable (labelLocalizedKernel label g) (μ.prod μ) := by
  have he : labelLocalizedKernel label g =
      {z : X × X | label z.1 = label z.2}.indicator (fun z => g z.2) := by
    funext z
    simp [labelLocalizedKernel, Set.indicator_apply]
  rw [he]
  exact (hg.comp_snd μ).indicator
    (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))

omit hlabel in
theorem labelLocalizedKernel_row (g : X → ℝ) (x : X) :
    (∫ y, labelLocalizedKernel label g (x, y) ∂μ) =
      ∫ y, (label ⁻¹' {label x}).indicator g y ∂μ := by
  congr 1
  funext y
  simp [labelLocalizedKernel, Set.indicator_apply, eq_comm]

theorem partition_mass_integrable :
    Integrable (fun x => μ.real (label ⁻¹' {label x})) μ := by
  have hm : Measurable (fun x => μ.real (label ⁻¹' {label x})) :=
    (measurable_of_countable (fun c : B => μ.real (label ⁻¹' {c}))).comp hlabel
  apply (MemLp.of_bound hm.aestronglyMeasurable 1 (p := 1) ?_).integrable (by norm_num)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

theorem labelLocalizedKernel_integral_le (g : X → ℝ) (hg : Integrable g μ)
    (M : ℝ) (hloc : ∀ c : B,
      (∫ x, (label ⁻¹' {c}).indicator g x ∂μ) ≤ M * μ.real (label ⁻¹' {c})) :
    (∫ z, labelLocalizedKernel label g z ∂μ.prod μ) ≤
      M * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  rw [integral_prod _ (labelLocalizedKernel_integrable μ label hlabel g hg)]
  simp_rw [labelLocalizedKernel_row μ label g]
  have hi := (labelLocalizedKernel_integrable μ label hlabel g hg).integral_prod_left
  simp_rw [labelLocalizedKernel_row μ label g] at hi
  calc
    _ ≤ ∫ x, M * μ.real (label ⁻¹' {label x}) ∂μ := by
      apply integral_mono hi ((partition_mass_integrable μ label hlabel).const_mul M)
      exact fun x => hloc (label x)
    _ = _ := by
      rw [integral_const_mul,
        finite_label_integral μ label hlabel (fun c => μ.real (label ⁻¹' {c}))]
      simp only [pow_two]

theorem labelLocalizedKernel_integral (g : X → ℝ) (hg : Integrable g μ) :
    (∫ z, labelLocalizedKernel label g z ∂μ.prod μ) =
      ∑ c : B, μ.real (label ⁻¹' {c}) *
        (∫ x, (label ⁻¹' {c}).indicator g x ∂μ) := by
  rw [integral_prod _ (labelLocalizedKernel_integrable μ label hlabel g hg)]
  simp_rw [labelLocalizedKernel_row μ label g]
  exact finite_label_integral μ label hlabel
    (fun c => ∫ x, (label ⁻¹' {c}).indicator g x ∂μ)

omit hlabel in
theorem sameLabelKernel_mul_eq_sum (r : X → ℝ) (z : X × X) :
    sameLabelKernel label z * r z.1 * r z.2 =
      ∑ c : B, (label ⁻¹' {c}).indicator r z.1 * (label ⁻¹' {c}).indicator r z.2 := by
  rw [Finset.sum_eq_single (label z.1)]
  · by_cases he : label z.1 = label z.2
    · simp [sameLabelKernel, Set.indicator_apply, he]
    · simp [sameLabelKernel, Set.indicator_apply, he, Ne.symm he]
  · intro c hc hne
    have hn : label z.1 ≠ c := Ne.symm hne
    simp [Set.indicator_apply, hn]
  · simp

theorem sameLabelKernel_mul_integrable (r : X → ℝ) (hr : Integrable r μ) :
    Integrable (fun z => sameLabelKernel label z * r z.1 * r z.2) (μ.prod μ) := by
  simp_rw [sameLabelKernel_mul_eq_sum label r]
  apply integrable_finsetSum
  intro c hc
  exact (hr.indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
    (hr.indicator ((measurableSet_singleton _).preimage hlabel))

theorem sameLabelKernel_mul_integral (r : X → ℝ) (hr : Integrable r μ) :
    (∫ z, sameLabelKernel label z * r z.1 * r z.2 ∂μ.prod μ) =
      ∑ c : B, (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 := by
  simp_rw [sameLabelKernel_mul_eq_sum label r]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [integral_prod_mul]
    ring
  · intro c hc
    exact (hr.indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
      (hr.indicator ((measurableSet_singleton _).preimage hlabel))

def pairWindowScore (r : X → ℝ) (V : ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then (r z.1 - r z.2) ^ 2 / 2 - V else 0

theorem pairWindowScore_measurable (r : X → ℝ) (hr : Measurable r) (V : ℝ) :
    Measurable (pairWindowScore label r V) := by
  unfold pairWindowScore
  exact Measurable.ite
    (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
    ((((hr.comp measurable_fst).sub (hr.comp measurable_snd)).pow_const 2
      |>.div_const 2).sub measurable_const) measurable_const

omit hlabel in
theorem pairWindowScore_symmetric (r : X → ℝ) (V : ℝ) (x y : X) :
    pairWindowScore label r V (x, y) = pairWindowScore label r V (y, x) := by
  unfold pairWindowScore
  simp only [Prod.fst, Prod.snd, eq_comm]
  split_ifs <;> ring

omit hlabel in
theorem pairWindowScore_abs_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    |pairWindowScore label r V z| ≤ r z.1 ^ 2 + r z.2 ^ 2 + |V| := by
  unfold pairWindowScore
  split_ifs with h
  · calc
      _ ≤ |(r z.1 - r z.2) ^ 2 / 2| + |V| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (r z.1 - r z.2) ^ 2 / 2)]
        nlinarith [sq_nonneg (r z.1 + r z.2)]
  · simp only [abs_zero]
    positivity

omit hlabel in
theorem pairWindowScore_sq_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    pairWindowScore label r V z ^ 2 ≤
      4 * (r z.1 ^ 4 + r z.2 ^ 4) + 2 * V ^ 2 := by
  unfold pairWindowScore
  split_ifs with h
  · have h1 := add_sq_le (a := (r z.1 - r z.2) ^ 2 / 2) (b := -V)
    have h2 := (show Even (4 : ℕ) by decide).add_pow_le
      (a := r z.1) (b := -r z.2)
    norm_num at h2
    nlinarith
  · simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

theorem pairWindowScore_memLp (r : X → ℝ) (hr : Measurable r) (V : ℝ)
    (h4 : Integrable (fun x => r x ^ 4) μ) :
    MemLp (pairWindowScore label r V) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq
    (pairWindowScore_measurable label hlabel r hr V).aestronglyMeasurable).mpr
  have hd : Integrable (fun z : X × X =>
      4 * (r z.1 ^ 4 + r z.2 ^ 4) + 2 * V ^ 2) (μ.prod μ) :=
    (((h4.comp_fst μ).add (h4.comp_snd μ)).const_mul 4).add (integrable_const _)
  apply hd.mono'
    ((pairWindowScore_measurable label hlabel r hr V).pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pairWindowScore_sq_le label r V z

omit hlabel in
theorem pairWindowScore_local_sq_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    pairWindowScore label r V z ^ 2 ≤
      4 * (labelLocalizedKernel label (fun x => r x ^ 4) z +
        labelLocalizedKernel label (fun x => r x ^ 4) z.swap) +
      2 * V ^ 2 * sameLabelKernel label z := by
  by_cases h : label z.1 = label z.2
  · have hb := pairWindowScore_sq_le label r V z
    simp only [pairWindowScore, labelLocalizedKernel, sameLabelKernel,
      Prod.fst_swap, Prod.snd_swap, if_pos h, if_pos h.symm] at hb ⊢
    nlinarith
  · simp [pairWindowScore, labelLocalizedKernel, sameLabelKernel, h, Ne.symm h]

theorem pairWindowScore_energy_le (r : X → ℝ) (hr : Measurable r) (V M4 : ℝ)
    (h4 : Integrable (fun x => r x ^ 4) μ)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 4) x ∂μ) ≤
      M4 * μ.real (label ⁻¹' {c})) :
    (∫ z, pairWindowScore label r V z ^ 2 ∂μ.prod μ) ≤
      (8 * M4 + 2 * V ^ 2) * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  let L := labelLocalizedKernel label (fun x => r x ^ 4)
  have hiL : Integrable L (μ.prod μ) :=
    labelLocalizedKernel_integrable μ label hlabel _ h4
  have hiD := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hd : Integrable (fun z : X × X => 4 * (L z + L z.swap) +
      2 * V ^ 2 * sameLabelKernel label z) (μ.prod μ) :=
    ((hiL.add hiL.swap).const_mul 4).add (hiD.const_mul _)
  have hb := integral_mono (pairWindowScore_memLp μ label hlabel r hr V h4).integrable_sq
    hd (pairWindowScore_local_sq_le label r V)
  rw [integral_add
      (f := fun z : X × X => 4 * (L z + L z.swap))
      (g := fun z => 2 * V ^ 2 * sameLabelKernel label z)
      ((hiL.add hiL.swap).const_mul 4) (hiD.const_mul _),
    integral_const_mul, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul, sameLabelKernel_integral μ label hlabel] at hb
  have hL := labelLocalizedKernel_integral_le μ label hlabel _ h4 M4 hloc
  dsimp [L] at hb
  nlinarith

theorem pairWindowScore_row_abs_le (r : X → ℝ) (hr : Measurable r) (V M2 : ℝ)
    (h2 : Integrable (fun x => r x ^ 2) μ)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) ≤
      M2 * μ.real (label ⁻¹' {c})) (x : X) :
    |∫ y, pairWindowScore label r V (x, y) ∂μ| ≤
      μ.real (label ⁻¹' {label x}) * (r x ^ 2 + |V| + M2) := by
  let A := label ⁻¹' {label x}
  have hA : MeasurableSet A := (measurableSet_singleton _).preimage hlabel
  let e : X → ℝ := fun y => A.indicator (fun y => r x ^ 2 + r y ^ 2 + |V|) y
  have hiE : Integrable e μ :=
    (((integrable_const (r x ^ 2)).add h2).add (integrable_const |V|)).indicator hA
  have hpoint : ∀ y, ‖pairWindowScore label r V (x, y)‖ ≤ e y := by
    intro y
    by_cases he : label x = label y
    · simpa only [Real.norm_eq_abs, e, A, Set.indicator_of_mem
        (show y ∈ A from he.symm)] using pairWindowScore_abs_le label r V (x, y)
    · simp [pairWindowScore, e, A, Set.indicator_apply, he, Ne.symm he]
  have hiS : Integrable (fun y => pairWindowScore label r V (x, y)) μ := by
    apply hiE.mono' ((pairWindowScore_measurable label hlabel r hr V).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Eventually.of_forall hpoint
  have hb : |∫ y, pairWindowScore label r V (x, y) ∂μ| ≤ ∫ y, e y ∂μ := by
    calc
      _ = ‖∫ y, pairWindowScore label r V (x, y) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖pairWindowScore label r V (x, y)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ _ := integral_mono hiS.norm hiE hpoint
  have heq : (∫ y, e y ∂μ) = μ.real A * (r x ^ 2 + |V|) +
      ∫ y, A.indicator (fun y => r y ^ 2) y ∂μ := by
    dsimp [e]
    rw [integral_indicator hA]
    have he : (fun y => r x ^ 2 + r y ^ 2 + |V|) =
        (fun y => (r x ^ 2 + |V|) + r y ^ 2) := by funext y; ring
    rw [he, integral_add (integrable_const _) h2.restrict,
      integral_const, ← integral_indicator hA]
    simp only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  rw [heq] at hb
  have hl := hloc (label x)
  dsimp [A] at hb
  nlinarith

theorem pairWindowScore_row_energy_le (r : X → ℝ) (hr : Measurable r)
    (V M2 M4 cap : ℝ) (hM2 : 0 ≤ M2) (hcap : 0 ≤ cap)
    (h2 : Integrable (fun x => r x ^ 2) μ)
    (h4 : Integrable (fun x => r x ^ 4) μ)
    (hglobal : (∫ x, r x ^ 4 ∂μ) ≤ M4)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) ≤
      M2 * μ.real (label ⁻¹' {c}))
    (hmass : ∀ c : B, μ.real (label ⁻¹' {c}) ≤ cap) :
    (∫ x, (∫ y, pairWindowScore label r V (x, y) ∂μ) ^ 2 ∂μ) ≤
      2 * cap ^ 2 * (M4 + (|V| + M2) ^ 2) := by
  have hi := PairUStatistic.rowIntegral_sq_integrable
    (pairWindowScore_memLp μ label hlabel r hr V h4)
  have hd : Integrable (fun x => 2 * cap ^ 2 * (r x ^ 4 + (|V| + M2) ^ 2)) μ :=
    (h4.add (integrable_const _)).const_mul _
  have hp : ∀ x, (∫ y, pairWindowScore label r V (x, y) ∂μ) ^ 2 ≤
      2 * cap ^ 2 * (r x ^ 4 + (|V| + M2) ^ 2) := by
    intro x
    let p := μ.real (label ⁻¹' {label x})
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hpc : p ≤ cap := hmass (label x)
    have hb := pairWindowScore_row_abs_le μ label hlabel r hr V M2 h2 hloc x
    have hA : 0 ≤ |V| + M2 := add_nonneg (abs_nonneg _) hM2
    calc
      _ = |∫ y, pairWindowScore label r V (x, y) ∂μ| ^ 2 := (sq_abs _).symm
      _ ≤ (p * (r x ^ 2 + |V| + M2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = p ^ 2 * (r x ^ 2 + (|V| + M2)) ^ 2 := by ring
      _ ≤ cap ^ 2 * (r x ^ 2 + (|V| + M2)) ^ 2 := by gcongr
      _ ≤ cap ^ 2 * (2 * ((r x ^ 2) ^ 2 + (|V| + M2) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left add_sq_le (sq_nonneg cap)
      _ = _ := by ring
  have hb := integral_mono hi hd hp
  rw [integral_const_mul, integral_add h4 (integrable_const _), integral_const] at hb
  simp at hb
  have hc2 : 0 ≤ 2 * cap ^ 2 := by positivity
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hglobal le_rfl) hc2)

theorem pairWindowScore_integral (r : X → ℝ) (hr : Measurable r) (V : ℝ)
    (hr2 : MemLp r 2 μ) :
    (∫ z, pairWindowScore label r V z ∂μ.prod μ) =
      ∑ c : B, (μ.real (label ⁻¹' {c}) *
        (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) -
        (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 -
        V * μ.real (label ⁻¹' {c}) ^ 2) := by
  let L := labelLocalizedKernel label (fun x => r x ^ 2)
  let Q := fun z : X × X => sameLabelKernel label z * r z.1 * r z.2
  have hiL : Integrable L (μ.prod μ) :=
    labelLocalizedKernel_integrable μ label hlabel _ hr2.integrable_sq
  have hiQ : Integrable Q (μ.prod μ) :=
    sameLabelKernel_mul_integrable μ label hlabel r (hr2.integrable (by norm_num))
  have hiD := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have heq : pairWindowScore label r V =
      (fun z : X × X => (L z + L z.swap) / 2 - Q z - V * sameLabelKernel label z) := by
    funext z
    dsimp [pairWindowScore, L, Q, labelLocalizedKernel, sameLabelKernel]
    by_cases he : label z.1 = label z.2
    · simp only [ite_eq_left he, ite_eq_left he.symm, one_mul]
      ring
    · simp [he, Ne.symm he]
  rw [heq, integral_sub
      (f := fun z : X × X => (L z + L z.swap) / 2 - Q z)
      (g := fun z => V * sameLabelKernel label z)
      (((hiL.add hiL.swap).div_const 2).sub hiQ) (hiD.const_mul V),
    integral_sub (f := fun z : X × X => (L z + L z.swap) / 2) (g := Q)
      ((hiL.add hiL.swap).div_const 2) hiQ,
    integral_div, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul]
  dsimp [L, Q]
  rw [labelLocalizedKernel_integral μ label hlabel _ hr2.integrable_sq,
    sameLabelKernel_mul_integral μ label hlabel r (hr2.integrable (by norm_num)),
    sameLabelKernel_integral μ label hlabel]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Partition
end NearlyMinimax
