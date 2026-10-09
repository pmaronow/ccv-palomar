module

public import Mathlib


@[expose] public section

/-! Independent fair signs attached to the cells of a finite random partition.
The sign law and all of its moments are constructed here, rather than assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def fairSignValue (b : Fin 2) : ℝ := if b = 0 then 1 else -1

def fairSignLaw : Measure (Fin 2) :=
  ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac 0 +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac 1

instance fairSignLaw_probability : IsProbabilityMeasure fairSignLaw := by
  constructor
  change (fairSignLaw Set.univ) = 1
  simp only [fairSignLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem fairSign_integrable (f : Fin 2 → ℝ) : Integrable f fairSignLaw := by
  unfold fairSignLaw
  exact ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

theorem fairSign_integral (f : Fin 2 → ℝ) :
    (∫ b, f b ∂fairSignLaw) = (f 0 + f 1) / 2 := by
  unfold fairSignLaw
  rw [integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    norm_num
    ring
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem fairSignValue_abs (b : Fin 2) : |fairSignValue b| = 1 := by
  fin_cases b <;> norm_num [fairSignValue]

theorem fairSignValue_sq (b : Fin 2) : fairSignValue b ^ 2 = 1 := by
  fin_cases b <;> norm_num [fairSignValue]

theorem fairSign_mean : (∫ b, fairSignValue b ∂fairSignLaw) = 0 := by
  rw [fairSign_integral]
  norm_num [fairSignValue]

theorem fairSign_power_moment (k : ℕ) :
    (∫ b, fairSignValue b ^ k ∂fairSignLaw) = if Even k then 1 else 0 := by
  rw [fairSign_integral]
  simp only [fairSignValue]
  norm_num
  by_cases h : Even k
  · simp [h, h.neg_one_pow]
  · have ho : Odd k := Nat.not_even_iff_odd.mp h
    simp [h, ho.neg_one_pow]

def cellSignLaw (I : Type*) [Fintype I] : Measure (I → Fin 2) :=
  Measure.pi (fun _ => fairSignLaw)

instance cellSignLaw_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (cellSignLaw I) := by
  unfold cellSignLaw
  infer_instance

theorem cellSign_mean {I : Type*} [Fintype I] (i : I) :
    (∫ b, fairSignValue (b i) ∂cellSignLaw I) = 0 := by
  change (∫ b, fairSignValue (b i) ∂Measure.pi (fun _ : I => fairSignLaw)) = 0
  rw [integral_comp_eval (μ := fun _ : I => fairSignLaw)
    (f := fairSignValue) (i := i) (by fun_prop)]
  exact fairSign_mean

theorem cellSign_covariance {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    (∫ b, fairSignValue (b i) * fairSignValue (b j) ∂cellSignLaw I) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl, ← pow_two, fairSignValue_sq]
    simp
  · have hi : IndepFun (fun b : I → Fin 2 => b i) (fun b : I → Fin 2 => b j)
        (cellSignLaw I) := by
      exact (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).indepFun hij
    rw [hi.integral_fun_comp_mul_comp (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable (Measurable.of_discrete.aestronglyMeasurable)
      (Measurable.of_discrete.aestronglyMeasurable)]
    simp [cellSign_mean, hij]

theorem cellSign_product_power_moment {I : Type*} [Fintype I] (k : I → ℕ) :
    (∫ b, ∏ i, fairSignValue (b i) ^ k i ∂cellSignLaw I) =
      ∏ i, if Even (k i) then (1 : ℝ) else 0 := by
  change (∫ b, ∏ i, fairSignValue (b i) ^ k i
    ∂Measure.pi (fun _ : I => fairSignLaw)) = _
  rw [integral_fintype_prod_eq_prod (fun i b => fairSignValue b ^ k i)]
  simp_rw [fairSign_power_moment]

theorem cellSign_product_moment {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (p : J → I) :
    (∫ b, ∏ j, fairSignValue (b (p j)) ∂cellSignLaw I) =
      if ∀ i, Even ((Finset.univ.filter (fun j => p j = i)).card) then (1 : ℝ) else 0 := by
  classical
  have he (b : I → Fin 2) : (∏ j, fairSignValue (b (p j))) =
      ∏ i, fairSignValue (b i) ^ (Finset.univ.filter (fun j => p j = i)).card := by
    rw [← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.univ)
      (g := p) (fun _ _ => Finset.mem_univ _) (fun i => fairSignValue (b i))]
    simp only [Finset.prod_const, smul_eq_mul]
  simp_rw [he]
  rw [cellSign_product_power_moment, Fintype.prod_boole]

theorem cellSign_product_odd_moment {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (p : J → I) (hj : Odd (Fintype.card J)) :
    (∫ b, ∏ j, fairSignValue (b (p j)) ∂cellSignLaw I) = 0 := by
  classical
  rw [cellSign_product_moment]
  apply if_neg
  intro h
  have hc : Fintype.card J =
      ∑ i : I, (Finset.univ.filter (fun j => p j = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have he : Even (Fintype.card J) := by
    rw [hc]
    exact Finset.even_sum _ (fun i _ => h i)
  exact (Nat.not_even_iff_odd.mpr hj) he

end NearlyMinimax
