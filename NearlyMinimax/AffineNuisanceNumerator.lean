module

public import NearlyMinimax.LocalNuisanceRanges
public import NearlyMinimax.HighCompleteSourceTail


@[expose] public section

/-! Borel spatial dependence and continuous nuisance dependence of genuine
marked affine-reset response numerators. The input bounds concern primitive
legal resets and ternary probabilities, not the desired energy envelope. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {ι X E : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace X] [MeasurableSpace E] {n : ℕ}

def affineNuisanceIntegrand (activation : E → ℝ) (a η : ℝ)
    (slope intercept : E → X → Fin n → ℝ)
    (vector : E → ι → ℝ) (time : E → ℝ)
    (w : X → Fin n → ℝ) (φ : X → Fin n → ι → ℝ)
    (z : LocalNuisance ι n) (x : X) (y : Fin n → Fin 3) (e : E) : ℝ :=
  activation e * (∏ i, (slope e x i * z.1 i + intercept e x i)) *
    highResponseProduct a z.2.2.2 η z.2.2.1 (w x) (φ x)
      (coefficientReset z.2.1 (vector e) (time e)) y

def affineNuisanceNumerator (π : Measure E) (activation : E → ℝ) (a η : ℝ)
    (slope intercept : E → X → Fin n → ℝ)
    (vector : E → ι → ℝ) (time : E → ℝ)
    (w : X → Fin n → ℝ) (φ : X → Fin n → ι → ℝ)
    (z : LocalNuisance ι n) (x : X) (y : Fin n → Fin 3) : ℝ :=
  (∫ e, affineNuisanceIntegrand activation a η slope intercept vector time w φ z x y e ∂π) -
    η^2 * (∏ i, z.1 i) * ∑ i, (w x i)^2 *
      highResponseVarianceTerm a z.2.2.2 η z.2.2.1 (w x) (φ x) z.2.1 y i

theorem ternaryMass_continuous_both {P : Type*} [TopologicalSpace P]
    (a : ℝ) (f V : P → ℝ) (hf : Continuous f) (hV : Continuous V) (y : Fin 3) :
    Continuous (fun p => ternaryMass a (f p) (V p) y) := by
  fin_cases y <;> simp only [ternaryMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons] <;> fun_prop

theorem affineNuisanceIntegrand_continuous (activation : E → ℝ) (a η : ℝ)
    (slope intercept : E → X → Fin n → ℝ)
    (vector : E → ι → ℝ) (time : E → ℝ)
    (w : X → Fin n → ℝ) (φ : X → Fin n → ι → ℝ)
    (x : X) (y : Fin n → Fin 3) (e : E) :
    Continuous (fun z : LocalNuisance ι n =>
      affineNuisanceIntegrand activation a η slope intercept vector time w φ z x y e) := by
  unfold affineNuisanceIntegrand highResponseProduct
  apply Continuous.mul
  · fun_prop
  · apply continuous_finset_prod
    intro i _
    apply ternaryMass_continuous_both
    · unfold coefficientRegression coefficientReset
      fun_prop
    · fun_prop

theorem affineNuisanceIntegrand_joint_measurable (activation : E → ℝ)
    (hact : Measurable activation) (a η : ℝ)
    (slope intercept : E → X → Fin n → ℝ)
    (hs : ∀ i, Measurable (fun xe : X × E => slope xe.2 xe.1 i))
    (hb : ∀ i, Measurable (fun xe : X × E => intercept xe.2 xe.1 i))
    (vector : E → ι → ℝ) (hv : ∀ γ, Measurable (fun e => vector e γ))
    (time : E → ℝ) (ht : Measurable time)
    (w : X → Fin n → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (φ : X → Fin n → ι → ℝ) (hφ : ∀ i γ, Measurable (fun x => φ x i γ))
    (z : LocalNuisance ι n) (y : Fin n → Fin 3) :
    Measurable (fun xe : X × E =>
      affineNuisanceIntegrand activation a η slope intercept vector time w φ z xe.1 y xe.2) := by
  unfold affineNuisanceIntegrand highResponseProduct
  apply Measurable.mul
  · exact (hact.comp measurable_snd).mul
      (Finset.measurable_fun_prod _ (fun i _ => (hs i).mul_const _ |>.add (hb i)))
  · apply Finset.measurable_fun_prod
    intro i _
    apply ternaryMass_measurable_comp
    unfold coefficientRegression coefficientReset
    have hw' : Measurable (fun xe : X × E => w xe.1 i) := (hw i).comp measurable_fst
    have ht' : Measurable (fun xe : X × E => time xe.2) := ht.comp measurable_snd
    have hv' (γ) : Measurable (fun xe : X × E => vector xe.2 γ) := (hv γ).comp measurable_snd
    have hφ' (γ) : Measurable (fun xe : X × E => φ xe.1 i γ) := (hφ i γ).comp measurable_fst
    fun_prop

theorem affineNuisanceNumerator_measurable (π : Measure E) [SFinite π]
    (activation : E → ℝ) (hact : Measurable activation) (a η : ℝ)
    (slope intercept : E → X → Fin n → ℝ)
    (hs : ∀ i, Measurable (fun xe : X × E => slope xe.2 xe.1 i))
    (hb : ∀ i, Measurable (fun xe : X × E => intercept xe.2 xe.1 i))
    (vector : E → ι → ℝ) (hv : ∀ γ, Measurable (fun e => vector e γ))
    (time : E → ℝ) (ht : Measurable time)
    (w : X → Fin n → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (φ : X → Fin n → ι → ℝ) (hφ : ∀ i γ, Measurable (fun x => φ x i γ))
    (z : LocalNuisance ι n) (y : Fin n → Fin 3) :
    Measurable (fun x => affineNuisanceNumerator π activation a η
      slope intercept vector time w φ z x y) := by
  have hI : Measurable (fun x => ∫ e,
      affineNuisanceIntegrand activation a η slope intercept vector time w φ z x y e ∂π) :=
    (affineNuisanceIntegrand_joint_measurable activation hact a η
      slope intercept hs hb vector hv time ht w hw φ hφ z y).stronglyMeasurable.integral_prod_right'.measurable
  unfold affineNuisanceNumerator
  apply hI.sub
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro i _
  apply (hw i).pow_const 2 |>.mul
  unfold highResponseVarianceTerm
  apply Measurable.const_mul
  apply Finset.measurable_fun_prod
  intro l _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  fun_prop

theorem affineNuisanceNumerator_continuousOn (π : Measure E)
    (activation : E → ℝ) (hact : Measurable activation) (hiAct : Integrable activation π)
    (ad bd C ρ v a η : ℝ) (had : 0 ≤ ad) (hab : ad ≤ bd) (hC : 0 < C) (ha : a ≠ 0)
    (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    (slope intercept : E → X → Fin n → ℝ)
    (hs : ∀ i, Measurable (fun xe : X × E => slope xe.2 xe.1 i))
    (hb : ∀ i, Measurable (fun xe : X × E => intercept xe.2 xe.1 i))
    (hreset : ∀ e x i p, p ∈ Icc ad bd → slope e x i*p+intercept e x i ∈ Icc ad bd)
    (vector : E → ι → ℝ) (hv : ∀ γ, Measurable (fun e => vector e γ))
    (hvb : ∀ e, ∑ γ, |vector e γ| ≤ C⁻¹)
    (time : E → ℝ) (ht : Measurable time) (htb : ∀ e, time e ∈ Icc (0 : ℝ) 1)
    (w : X → Fin n → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (hwb : ∀ x i, |w x i| ≤ 1)
    (φ : X → Fin n → ι → ℝ) (hφ : ∀ i γ, Measurable (fun x => φ x i γ))
    (hφb : ∀ x (c : ι → ℝ), (∑ γ, |c γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ x i γ*c γ| ≤ 1)
    (hp : ∀ f V, |f| ≤ ρ → |V-v| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (x : X) (y : Fin n → Fin 3) :
    ContinuousOn (fun z => affineNuisanceNumerator π activation a η
      slope intercept vector time w φ z x y) (localNuisanceSet ι n ad bd C ρ v) := by
  let K := localNuisanceSet ι n ad bd C ρ v
  have hI : ContinuousOn (fun z : LocalNuisance ι n => ∫ e,
      affineNuisanceIntegrand activation a η slope intercept vector time w φ z x y e ∂π) K := by
    apply continuousOn_of_dominated (bound := fun e => |activation e| * bd^n)
    · intro z hz
      exact ((affineNuisanceIntegrand_joint_measurable activation hact a η slope intercept hs hb
        vector hv time ht w hw φ hφ z y).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · intro z hz
      obtain ⟨hpz, hcz, hgz, hVz⟩ := localNuisanceSet_guards ι n ad bd C ρ v z hz
      apply Filter.Eventually.of_forall
      intro e
      have hden (i) : |slope e x i*z.1 i+intercept e x i| ≤ bd := by
        have hh := hreset e x i (z.1 i) (hpz i)
        rw [abs_of_nonneg (had.trans hh.1)]
        exact hh.2
      have hb0 : 0 ≤ bd := had.trans hab
      have hc : ∑ γ, |coefficientReset z.2.1 (vector e) (time e) γ| ≤ C⁻¹ :=
        coefficientReset_mem_ball C z.2.1 (vector e) (time e) (htb e) hcz (hvb e)
      have hprob := highResponseProduct_ball_abs_le_one C a z.2.2.2 η ρ ha hη hηρ
        z.2.2.1 (w x) (φ x) hgz (hwb x) (hφb x) (fun f hf => hp f _ hf hVz)
        (coefficientReset z.2.1 (vector e) (time e)) hc y
      change |affineNuisanceIntegrand activation a η slope intercept vector time w φ z x y e| ≤ _
      unfold affineNuisanceIntegrand
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left
        (finite_density_product_abs_bound _ bd hb0 hden) (abs_nonneg _)) hprob
        (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    · exact hiAct.abs.mul_const _
    · exact Filter.Eventually.of_forall (fun e =>
        (affineNuisanceIntegrand_continuous activation a η slope intercept vector time w φ x y e).continuousOn)
  have hheat : Continuous (fun z : LocalNuisance ι n =>
      η^2 * (∏ i, z.1 i) * ∑ i, (w x i)^2 *
        highResponseVarianceTerm a z.2.2.2 η z.2.2.1 (w x) (φ x) z.2.1 y i) := by
    apply Continuous.mul
    · fun_prop
    · apply continuous_finset_sum
      intro i _
      apply Continuous.const_mul
      unfold highResponseVarianceTerm
      apply Continuous.const_mul
      apply continuous_finset_prod
      intro l _
      apply ternaryMass_continuous_both
      · unfold coefficientRegression
        fun_prop
      · fun_prop
  exact hI.sub hheat.continuousOn

end
end NearlyMinimax
