module

public import NearlyMinimax.HistoryCanonicalDeletion


@[expose] public section

/-! Genuine independent finite mark histories preserve the mean of affine
updates. Integrability is derived by product Fubini, without a desired-history
integrability or expectation premise. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

def finiteAffineHistory {J E : Type*} (slope offset : J → E → ℝ)
    (n : ℕ) (labels : Fin n → J) (marks : Fin n → E) : ℝ :=
  (List.ofFn (fun i : Fin n => i)).foldl
    (fun value i => slope (labels i) (marks i) * value + offset (labels i) (marks i)) 1

theorem finiteAffineHistory_succ {J E : Type*} (slope offset : J → E → ℝ)
    (n : ℕ) (labels : Fin (n + 1) → J) (marks : Fin (n + 1) → E) :
    finiteAffineHistory slope offset (n + 1) labels marks =
      slope (labels (Fin.last n)) (marks (Fin.last n)) *
        finiteAffineHistory slope offset n (fun i => labels i.castSucc) (fun i => marks i.castSucc) +
      offset (labels (Fin.last n)) (marks (Fin.last n)) := by
  unfold finiteAffineHistory
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 2
  have hh : (List.ofFn (fun i : Fin n => i.castSucc)) =
      (List.ofFn (fun i : Fin n => i)).map Fin.castSucc := by rw [List.map_ofFn]; rfl
  rw [hh, List.foldl_map]

theorem finiteAffineHistory_measurable {J E : Type*} [MeasurableSpace E]
    (slope offset : J → E → ℝ) (hs : ∀ j, Measurable (slope j))
    (ho : ∀ j, Measurable (offset j)) (n : ℕ) (labels : Fin n → J) :
    Measurable (finiteAffineHistory slope offset n labels) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun marks => finiteAffineHistory slope offset (n + 1) labels marks)
    simp only [finiteAffineHistory_succ]
    exact ((hs _).comp (measurable_pi_apply _)).mul
      ((ih (fun i => labels i.castSucc)).comp (measurable_pi_iff.mpr
        (fun i : Fin n => measurable_pi_apply i.castSucc))) |>.add
      ((ho _).comp (measurable_pi_apply _))

theorem finiteAffineHistory_integrable {J E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (slope offset : J → E → ℝ)
    (hs : ∀ j, Integrable (slope j) π) (ho : ∀ j, Integrable (offset j) π)
    (n : ℕ) (labels : Fin n → J) :
    Integrable (finiteAffineHistory slope offset n labels) (Measure.pi (fun _ : Fin n => π)) := by
  induction n with
  | zero => exact integrable_const _
  | succ n ih =>
    let j := labels (Fin.last n)
    let f := finiteAffineHistory slope offset n (fun i => labels i.castSucc)
    have hi : Integrable (fun p : E × (Fin n → E) => slope j p.1 * f p.2 + offset j p.1)
        (π.prod (Measure.pi (fun _ : Fin n => π))) :=
      ((hs j).mul_prod (ih _)).add ((ho j).comp_fst _)
    apply ((historyFiniteMarkAppendEquiv_preserving n π).integrable_comp_emb
      (historyFiniteMarkAppendEquiv n).measurableEmbedding).mp
    convert hi using 1
    funext ⟨fresh, marks⟩
    simp only [Function.comp_apply, finiteAffineHistory_succ,
      historyFiniteMarkAppendEquiv_last, historyFiniteMarkAppendEquiv_old]
    rfl

theorem finiteAffineHistory_integral_one {J E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (slope offset : J → E → ℝ)
    (hs : ∀ j, Integrable (slope j) π) (ho : ∀ j, Integrable (offset j) π)
    (hmean : ∀ j, (∫ e, slope j e ∂π) + (∫ e, offset j e ∂π) = 1)
    (n : ℕ) (labels : Fin n → J) :
    (∫ marks, finiteAffineHistory slope offset n labels marks
      ∂Measure.pi (fun _ : Fin n => π)) = 1 := by
  induction n with
  | zero => simp only [finiteAffineHistory, List.ofFn_zero, List.foldl_nil, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
  | succ n ih =>
    let j := labels (Fin.last n)
    let f := finiteAffineHistory slope offset n (fun i => labels i.castSucc)
    rw [← (historyFiniteMarkAppendEquiv_preserving n π).integral_comp
      (historyFiniteMarkAppendEquiv n).measurableEmbedding]
    have he : (fun p : E × (Fin n → E) =>
        finiteAffineHistory slope offset (n + 1) labels (historyFiniteMarkAppendEquiv n p)) =
        (fun p => slope j p.1 * f p.2 + offset j p.1) := by
      funext ⟨fresh, marks⟩
      simp only [finiteAffineHistory_succ, historyFiniteMarkAppendEquiv_last,
        historyFiniteMarkAppendEquiv_old]
      rfl
    rw [he, integral_add ((hs j).mul_prod (finiteAffineHistory_integrable π slope offset hs ho n _))
      ((ho j).comp_fst _), integral_prod_mul, integral_fun_fst]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, ih, mul_one]
    exact hmean j

end NearlyMinimax
