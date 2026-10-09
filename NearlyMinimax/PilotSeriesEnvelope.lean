module

public import NearlyMinimax.PreconditionedPilot


@[expose] public section

/-! The actual finite factorial series and its maximum envelope. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

def dyadicPilotSeries {d : ℕ} (C : ModelConstants d) (A Λ : ℝ) (j m : ℕ) : ℝ :=
  ∑ k : Fin (m + anchoredDimension d C.order + 1),
    ((k.val + 1).factorial : ℝ) *
      (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
        preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (k.val + 1)

theorem dyadicPilotSeries_nonneg {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 ≤ Λ) (j m : ℕ) : 0 ≤ dyadicPilotSeries C A Λ j m := by
  unfold dyadicPilotSeries
  have hp := preconditionedPilotMomentConstant_pos C C.order
  have hk := dyadicPilotScale_pos d j
  positivity

def dyadicSeriesEnvelope {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (J : ℕ) (m : ℕ → ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (J + 1) =>
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val))

theorem dyadicSeriesEnvelope_level_le {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (J : ℕ) (m : ℕ → ℕ) (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val) ≤
      dyadicSeriesEnvelope C A Λ J m :=
  Finset.le_sup' (fun j : Fin (J + 1) =>
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val)) (Finset.mem_univ j)

theorem dyadicSeriesEnvelope_nonneg {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 ≤ Λ) (J : ℕ) (m : ℕ → ℕ) : 0 ≤ dyadicSeriesEnvelope C A Λ J m := by
  apply le_trans _ (dyadicSeriesEnvelope_level_le C A Λ J m ⟨0, by omega⟩)
  exact mul_nonneg (dyadicPilotSeries_nonneg C A Λ hΛ _ _) (zero_le_one.trans (le_max_left _ _))

theorem dyadicPilotSeries_le_envelope {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 ≤ Λ) (J : ℕ) (m : ℕ → ℕ) (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) ≤ dyadicSeriesEnvelope C A Λ J m := by
  have hnon := dyadicPilotSeries_nonneg C A Λ hΛ j.val (m j.val)
  apply le_trans _ (dyadicSeriesEnvelope_level_le C A Λ J m j)
  exact le_mul_of_one_le_right hnon (le_max_left _ _)

theorem dyadicPilotSeries_div_scale_le_envelope {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 < Λ) (J : ℕ) (m : ℕ → ℕ) (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) / dyadicPilotScale d j.val ≤
      dyadicSeriesEnvelope C A Λ J m / Λ := by
  have hnon := dyadicPilotSeries_nonneg C A Λ hΛ.le j.val (m j.val)
  have h := (mul_le_mul_of_nonneg_left (le_max_right 1 (Λ / dyadicPilotScale d j.val)) hnon).trans
    (dyadicSeriesEnvelope_level_le C A Λ J m j)
  apply (le_div_iff₀ hΛ).mpr
  convert h using 1 <;> ring

theorem dyadicPilotScale_parent_ratio_le {d j : ℕ} :
    dyadicPilotScale d j ≤ (2 : ℝ) ^ d * dyadicPilotScale d (j - 1) := by
  cases j with
  | zero => simpa [dyadicPilotScale] using one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  | succ j => simp only [Nat.add_sub_cancel, dyadicPilotScale, pow_succ, mul_pow]; exact le_of_eq (by ring)

end NearlyMinimax
