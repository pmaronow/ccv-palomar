module

public import Mathlib


@[expose] public section

/-! Centering contracts the squared L² norm of an actual multilinear iid kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RoughRegime.Centering

set_option backward.isDefEq.respectTransparency false

lemma bounded_vector_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ} (X : Ω → Fin p → ℝ)
    (hm : Measurable X) (M : ℝ) (_hM : 0 ≤ M) (hb : ∀ ω, ‖X ω‖ ≤ M) :
    Integrable X μ :=
  Integrable.of_bound hm.aestronglyMeasurable M (Filter.Eventually.of_forall hb)

theorem linear_centering_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ} (X : Ω → Fin p → ℝ)
    (hm : Measurable X) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω, ‖X ω‖ ≤ M)
    (m : Fin p → ℝ) (hmean : (∫ ω, X ω ∂μ) = m) (L : (Fin p → ℝ) →L[ℝ] ℝ) :
    (∫ ω, L (X ω - m) ^ 2 ∂μ) ≤ ∫ ω, L (X ω) ^ 2 ∂μ := by
  have hi := bounded_vector_integrable μ X hm M hM hb
  have hLX : Measurable (fun ω => L (X ω)) := L.continuous.measurable.comp hm
  have hml : (∫ ω, L (X ω) ∂μ) = L m := by rw [L.integral_comp_comm hi, hmean]
  have hv := variance_le_expectation_sq (μ := μ) hLX.aestronglyMeasurable
  rw [variance_eq_integral hLX.aemeasurable, hml] at hv
  simpa only [map_sub, Pi.pow_apply] using hv

lemma kernel_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (V : Ω → Fin r → Fin p → ℝ) (hm : Measurable V)
    (B : ℝ) (_hB : 0 ≤ B) (hb : ∀ᵐ ω ∂μ, ∀ i, ‖V ω i‖ ≤ B) :
    Integrable (fun ω => H (V ω) ^ 2) μ := by
  have hmeas : Measurable (fun ω => H (V ω) ^ 2) :=
    (H.coe_continuous.measurable.comp hm).pow_const 2
  apply Integrable.of_bound hmeas.aestronglyMeasurable ((‖H‖ * B ^ r) ^ 2)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_pow, ← Real.norm_eq_abs]
  apply pow_le_pow_left₀ (norm_nonneg _) _
  calc
    ‖H (V ω)‖ ≤ ‖H‖ * ∏ i, ‖V ω i‖ := H.le_opNorm _
    _ ≤ ‖H‖ * ∏ _i : Fin r, B := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hω i)
    _ = ‖H‖ * B ^ r := by simp

lemma integral_pi_succ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {r : ℕ}
    (f : (Fin (r + 1) → Ω) → ℝ) (hf : Integrable f (Measure.pi (fun _ => μ))) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin (r + 1) => μ)) =
      ∫ x, ∫ y, f (Fin.cons x y) ∂Measure.pi (fun _ : Fin r => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Ω) 0
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0
  have hf' : Integrable (f ∘ e.symm) (μ.prod (Measure.pi (fun _ : Fin r => μ))) :=
    (he.symm e).integrable_comp_of_integrable hf
  rw [← (he.symm e).integral_comp' f]
  change (∫ x, (f ∘ e.symm) x ∂μ.prod (Measure.pi (fun _ : Fin r => μ))) = _
  rw [integral_prod _ hf']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      apply congrArg f
      funext i
      cases i using Fin.cases <;> simp [e]

lemma kernel_cons_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin (r + 1) => Fin p → ℝ) ℝ)
    (A B : Ω → Fin p → ℝ) (hA : Measurable A) (hB : Measurable B)
    (C : ℝ) (hC : 0 ≤ C) (hbA : ∀ ω, ‖A ω‖ ≤ C) (hbB : ∀ ω, ‖B ω‖ ≤ C) :
    Integrable (fun xy : Ω × (Fin r → Ω) =>
      H (Fin.cons (A xy.1) (fun j => B (xy.2 j))) ^ 2)
      (μ.prod (Measure.pi (fun _ : Fin r => μ))) := by
  refine kernel_square_integrable _ H _ ?_ C hC ?_
  · apply measurable_pi_iff.mpr
    intro i
    cases i using Fin.cases
    · simpa only [Fin.cons_zero, Function.comp_def] using hA.comp measurable_fst
    · rename_i j
      simpa only [Fin.cons_succ, Function.comp_def] using
        hB.comp ((measurable_pi_apply j).comp measurable_snd)
  · exact Filter.Eventually.of_forall fun xy i => by
      cases i using Fin.cases
      · simpa using hbA xy.1
      · rename_i j
        simpa using hbB (xy.2 j)

theorem multilinear_iid_centering_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Ω → Fin p → ℝ) (hm : Measurable X) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ ω, ‖X ω‖ ≤ M) (m : Fin p → ℝ) (hmean : (∫ ω, X ω ∂μ) = m) :
    (∫ ω, H (fun j => X (ω j) - m) ^ 2 ∂Measure.pi (fun _ : Fin r => μ)) ≤
      ∫ ω, H (fun j => X (ω j)) ^ 2 ∂Measure.pi (fun _ : Fin r => μ) := by
  induction r with
  | zero =>
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext j
    exact Fin.elim0 j
  | succ r ih =>
    let Y : Ω → Fin p → ℝ := fun ω => X ω - m
    have hY : Measurable Y := hm.sub measurable_const
    let C := M + ‖m‖
    have hC : 0 ≤ C := add_nonneg hM (norm_nonneg _)
    have hbX : ∀ ω, ‖X ω‖ ≤ C := fun ω => (hb ω).trans (le_add_of_nonneg_right (norm_nonneg _))
    have hbY : ∀ ω, ‖Y ω‖ ≤ C := fun ω => (norm_sub_le _ _).trans (add_le_add (hb ω) le_rfl)
    have hc := kernel_cons_square_integrable μ H Y Y hY hY C hC hbY hbY
    have hmix := kernel_cons_square_integrable μ H X Y hm hY C hC hbX hbY
    have hu := kernel_cons_square_integrable μ H X X hm hm C hC hbX hbX
    have hiCenter : Integrable (fun ω : Fin (r + 1) → Ω => H (fun j => Y (ω j)) ^ 2)
        (Measure.pi (fun _ => μ)) := by
      apply kernel_square_integrable _ H _ (measurable_pi_iff.mpr fun j => hY.comp (measurable_pi_apply j)) C hC
      exact Filter.Eventually.of_forall fun ω j => hbY (ω j)
    have hiUncenter : Integrable (fun ω : Fin (r + 1) → Ω => H (fun j => X (ω j)) ^ 2)
        (Measure.pi (fun _ => μ)) := by
      apply kernel_square_integrable _ H _ (measurable_pi_iff.mpr fun j => hm.comp (measurable_pi_apply j)) C hC
      exact Filter.Eventually.of_forall fun ω j => hbX (ω j)
    calc
      _ = ∫ x, ∫ y, H (Fin.cons (Y x) (fun j => Y (y j))) ^ 2
          ∂Measure.pi (fun _ : Fin r => μ) ∂μ := by
        rw [integral_pi_succ μ _ hiCenter]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp
      _ = ∫ y, ∫ x, H (Fin.cons (Y x) (fun j => Y (y j))) ^ 2
          ∂μ ∂Measure.pi (fun _ : Fin r => μ) := integral_integral_swap hc
      _ ≤ ∫ y, ∫ x, H (Fin.cons (X x) (fun j => Y (y j))) ^ 2
          ∂μ ∂Measure.pi (fun _ : Fin r => μ) := by
        apply integral_mono_ae hc.integral_prod_right hmix.integral_prod_right
        exact Filter.Eventually.of_forall fun y => by
          let L : (Fin p → ℝ) →L[ℝ] ℝ :=
            (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Fin p → ℝ) ℝ
              (fun j => Y (y j))).comp H.curryLeft
          simpa only [L, ContinuousLinearMap.comp_apply,
            ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.curryLeft_apply]
            using linear_centering_square_le μ X hm M hM hb m hmean L
      _ = ∫ x, ∫ y, H (Fin.cons (X x) (fun j => Y (y j))) ^ 2
          ∂Measure.pi (fun _ : Fin r => μ) ∂μ := (integral_integral_swap hmix).symm
      _ ≤ ∫ x, ∫ y, H (Fin.cons (X x) (fun j => X (y j))) ^ 2
          ∂Measure.pi (fun _ : Fin r => μ) ∂μ := by
        apply integral_mono_ae hmix.integral_prod_left hu.integral_prod_left
        exact Filter.Eventually.of_forall fun x => by
          simpa only [ContinuousMultilinearMap.curryLeft_apply] using ih (H.curryLeft (X x))
      _ = _ := by
        rw [integral_pi_succ μ _ hiUncenter]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp

/-- The product-law contraction applies to iid vectors on any probability space. -/
theorem independent_centering_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin r → Ω → Fin p → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ i ω, ‖X i ω‖ ≤ M)
    (m : Fin p → ℝ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = m) :
    (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) ≤ ∫ ω, H (fun i => X i ω) ^ 2 ∂μ := by
  by_cases hr : r = 0
  · subst r
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext i
    exact Fin.elim0 i
  · let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hcopy : Measurable (fun ω : Fin r → Ω => fun i => X j (ω i)) :=
      measurable_pi_iff.mpr fun i => (hm j).comp (measurable_pi_apply i)
    have hjoint : Measurable (fun ω => fun i => X i ω) :=
      measurable_pi_iff.mpr hm
    have hjointLaw : IdentDistrib (fun ω => fun i => X i ω)
        (fun ω : Fin r → Ω => fun i => X j (ω i)) μ (Measure.pi (fun _ => μ)) := by
      refine ⟨hjoint.aemeasurable, hcopy.aemeasurable, ?_⟩
      rw [hind.map_fun_eq_pi_map (fun i => (hm i).aemeasurable),
        Measure.pi_map_pi (fun _ => (hm j).aemeasurable)]
      congr 1
      funext i
      exact (hid i j).map_eq
    have hc : Measurable (fun v : Fin r → Fin p → ℝ => H (fun i => v i - m) ^ 2) :=
      (H.coe_continuous.measurable.comp
        (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).sub measurable_const)).pow_const 2
    have hu : Measurable (fun v : Fin r → Fin p → ℝ => H v ^ 2) :=
      H.coe_continuous.measurable.pow_const 2
    have hcEq : (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) =
        ∫ ω, H (fun i => X j (ω i) - m) ^ 2 ∂Measure.pi (fun _ : Fin r => μ) := by
      simpa only [Function.comp_def] using (hjointLaw.comp hc).integral_eq
    have huEq : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) =
        ∫ ω, H (fun i => X j (ω i)) ^ 2 ∂Measure.pi (fun _ : Fin r => μ) := by
      simpa only [Function.comp_def] using (hjointLaw.comp hu).integral_eq
    rw [hcEq, huEq]
    exact multilinear_iid_centering_square_le μ H (X j) (hm j) M hM (hb j) m (hmean j)

end RoughRegime.Centering
