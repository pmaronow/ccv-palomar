module

public import NearlyMinimax.OscillationMGF
public import NearlyMinimax.HistoryCanonicalDeletion


@[expose] public section

/-!
# Genuine finite-product bounded differences
-/

noncomputable section
open MeasureTheory Set Filter
namespace NearlyMinimax

variable {E : Type*} [MeasurableSpace E] [Nonempty E]

omit [Nonempty E] in
/-- The finite independent insertion is exactly the ordinary last-coordinate tuple recursion. -/
theorem finiteMarkAppend_eq_snoc (n : ℕ) (fresh : E) (marks : Fin n → E) :
    historyFiniteMarkAppendEquiv n (fresh, marks) = Fin.snoc marks fresh := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [historyFiniteMarkAppendEquiv_last, Fin.snoc_last]
  · rw [historyFiniteMarkAppendEquiv_old, Fin.snoc_castSucc]

omit [Nonempty E] in
/-- Independent last-coordinate insertion preserves the genuine product law, allowing nonidentical laws. -/
theorem finiteMarkAppend_preserving_varying (n : ℕ) (π : Fin (n + 1) → Measure E)
    [∀ i, IsProbabilityMeasure (π i)] :
    MeasurePreserving (historyFiniteMarkAppendEquiv n (E := E))
      ((π (Fin.last n)).prod (Measure.pi (fun i : Fin n => π i.castSucc))) (Measure.pi π) := by
  simpa only [historyFiniteMarkAppendEquiv, Fin.succAbove_last_apply] using
    (measurePreserving_piFinSuccAbove π (Fin.last n)).symm _

/-- The uncentered one-coordinate exponential bound follows from the proved oscillation lemma. -/
theorem exp_integral_le_of_oscillation (π : Measure E) [IsProbabilityMeasure π]
    (X : E → ℝ) (hX : Measurable X) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ e, |X e| ≤ R) (hosc : ∀ e f, |X e - X f| ≤ c) (u : ℝ) :
    (∫ e, Real.exp (u * X e) ∂π) ≤
      Real.exp (u * ∫ e, X e ∂π) * Real.exp (u ^ 2 * c ^ 2 / 8) := by
  have hh := centered_mgf_le_of_oscillation π X hX R c hc hbound hosc u
  have hf : (fun e => Real.exp (u * X e)) =
      (fun e => Real.exp (u * ∫ f, X f ∂π) * Real.exp (u * (X e - ∫ f, X f ∂π))) := by
    funext e
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf, integral_const_mul]
  exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

/-- True McDiarmid moment bound for an arbitrary bounded measurable function of finite independent blocks.
Only the actual coordinate oscillation is an input; the concentration inequality is proved. -/
theorem product_exp_integral_le (n : ℕ) (π : Fin n → Measure E)
    [∀ i, IsProbabilityMeasure (π i)]
    (F : (Fin n → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ i x y, |F (Function.update x i y) - F x| ≤ c) (u : ℝ) :
    (∫ x, Real.exp (u * F x) ∂Measure.pi π) ≤
      Real.exp (u * ∫ x, F x ∂Measure.pi π) * Real.exp ((n : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  induction n with
  | zero =>
    let empty : Fin 0 → E := Fin.elim0
    have hf : F = fun _ => F empty := by funext x; congr 1; exact Subsingleton.elim _ _
    rw [hf]
    simp
  | succ n ih =>
    let ν := π (Fin.last n)
    let μ := Measure.pi (fun i : Fin n => π i.castSucc)
    let e := historyFiniteMarkAppendEquiv n (E := E)
    have hp : MeasurePreserving e (ν.prod μ) (Measure.pi π) := finiteMarkAppend_preserving_varying n π
    let H := fun p : E × (Fin n → E) => F (e p)
    have hH : Measurable H := hF.comp e.measurable
    have hHi : Integrable H (ν.prod μ) := Integrable.of_bound hH.aestronglyMeasurable R
      (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hbound (e p))
    let G := fun x : Fin n → E => ∫ y, H (y, x) ∂ν
    have hG : Measurable G := hH.stronglyMeasurable.integral_prod_left'.measurable
    have hXi : ∀ x, Integrable (fun y => H (y, x)) ν := by
      intro x
      apply Integrable.of_bound (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable R
      exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, Function.comp_apply, Prod.map_apply, id_eq, H] using hbound (e (y, x))
    have hGb : ∀ x, |G x| ≤ R := by
      intro x
      simpa [G, Real.norm_eq_abs] using
        norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => H (y, x)) (C := R)
          (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, H] using hbound (e (y, x)))
    have hGo : ∀ i x y, |G (Function.update x i y) - G x| ≤ c := by
      intro i x y
      change |(∫ z, H (z, Function.update x i y) ∂ν) - ∫ z, H (z, x) ∂ν| ≤ c
      rw [← integral_sub (hXi _) (hXi _)]
      have hb : ∀ᵐ z ∂ν, ‖H (z, Function.update x i y) - H (z, x)‖ ≤ c := by
        apply Eventually.of_forall
        intro z
        simpa only [H, e, finiteMarkAppend_eq_snoc, Fin.snoc_update, Real.norm_eq_abs] using
          hosc i.castSucc (Fin.snoc x z) y
      simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hb
    have hXo : ∀ x y z, |H (y, x) - H (z, x)| ≤ c := by
      intro x y z
      simpa only [H, e, finiteMarkAppend_eq_snoc, Fin.update_snoc_last] using
        hosc (Fin.last n) (Fin.snoc x z) y
    have hpoint : ∀ x, (∫ y, Real.exp (u * H (y, x)) ∂ν) ≤
        Real.exp (u * G x) * Real.exp (u ^ 2 * c ^ 2 / 8) := by
      intro x
      exact exp_integral_le_of_oscillation ν (fun y => H (y, x))
        (hH.comp (measurable_id.prodMk measurable_const)) R c hc
        (fun y => hbound (e (y, x))) (hXo x) u
    have hmean : (∫ x, F x ∂Measure.pi π) = ∫ x, G x ∂μ := by
      rw [← hp.integral_comp' F, integral_prod_symm H hHi]
    have hEi : Integrable (fun p => Real.exp (u * H p)) (ν.prod μ) := by
      apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul hH)).aestronglyMeasurable
        (Real.exp (|u| * R))
      apply Eventually.of_forall
      intro p
      change ‖Real.exp (u * H p)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbound (e p)) (abs_nonneg u))
    have hEGi : Integrable (fun x => Real.exp (u * G x)) μ := by
      apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul hG)).aestronglyMeasurable
        (Real.exp (|u| * R))
      apply Eventually.of_forall
      intro x
      change ‖Real.exp (u * G x)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hGb x) (abs_nonneg u))
    rw [← hp.integral_comp' (fun x => Real.exp (u * F x)), integral_prod_symm _ hEi, hmean]
    calc
      _ ≤ ∫ x, Real.exp (u * G x) * Real.exp (u ^ 2 * c ^ 2 / 8) ∂μ :=
        integral_mono (hEi.integral_prod_right) (hEGi.mul_const _) hpoint
      _ = (∫ x, Real.exp (u * G x) ∂μ) * Real.exp (u ^ 2 * c ^ 2 / 8) := integral_mul_const _ _
      _ ≤ (Real.exp (u * ∫ x, G x ∂μ) * Real.exp ((n : ℝ) * u ^ 2 * c ^ 2 / 8)) *
          Real.exp (u ^ 2 * c ^ 2 / 8) :=
        mul_le_mul_of_nonneg_right (ih (fun i : Fin n => π i.castSucc) G hG hGb hGo) (Real.exp_pos _).le
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring

/-- Centering gives the exact source exponent N c² u²/8. -/
theorem product_centered_mgf_le (n : ℕ) (π : Fin n → Measure E)
    [∀ i, IsProbabilityMeasure (π i)]
    (F : (Fin n → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ i x y, |F (Function.update x i y) - F x| ≤ c) (u : ℝ) :
    (∫ x, Real.exp (u * (F x - ∫ y, F y ∂Measure.pi π)) ∂Measure.pi π) ≤
      Real.exp ((n : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  have hh := product_exp_integral_le n π F hF R c hc hbound hosc u
  let m := ∫ y, F y ∂Measure.pi π
  have hf : (fun x => Real.exp (u * (F x - m))) =
      (fun x => Real.exp (-u * m) * Real.exp (u * F x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫ x, Real.exp (u * (F x - m)) ∂Measure.pi π) ≤ _
  rw [hf, integral_const_mul]
  have hprod : Real.exp (-u * m) * Real.exp (u * m) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ ≤ Real.exp (-u * m) *
        (Real.exp (u * m) * Real.exp ((n : ℝ) * u ^ 2 * c ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, hprod, one_mul]

end NearlyMinimax
