module

public import NearlyMinimax.AffineNuisanceNumerator


@[expose] public section

/-! Joint Borel dependence of genuine marked numerators in nuisance and
spatial coordinates, proved directly from their polynomial formulas. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
section
variable {ι X E : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace X] [MeasurableSpace E] {n : ℕ}

theorem ternaryMass_measurable_both {P : Type*} [MeasurableSpace P]
    (a : ℝ) (f V : P → ℝ) (hf : Measurable f) (hV : Measurable V) (y : Fin 3) :
    Measurable (fun p => ternaryMass a (f p) (V p) y) := by
  fin_cases y <;> simp only [ternaryMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons] <;> fun_prop

theorem affineNuisanceIntegrand_all_joint_measurable
    (activation : E → ℝ) (hact : Measurable activation) (a η : ℝ)
    (slope intercept : E → X → Fin n → ℝ)
    (hs : ∀ i, Measurable (fun xe : X × E => slope xe.2 xe.1 i))
    (hb : ∀ i, Measurable (fun xe : X × E => intercept xe.2 xe.1 i))
    (vector : E → ι → ℝ) (hv : ∀ γ, Measurable (fun e => vector e γ))
    (time : E → ℝ) (ht : Measurable time)
    (w : X → Fin n → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (φ : X → Fin n → ι → ℝ) (hφ : ∀ i γ, Measurable (fun x => φ x i γ))
    (y : Fin n → Fin 3) :
    Measurable (fun zxe : (LocalNuisance ι n × X) × E =>
      affineNuisanceIntegrand activation a η slope intercept vector time w φ
        zxe.1.1 zxe.1.2 y zxe.2) := by
  have hz : Measurable (fun zxe : (LocalNuisance ι n × X) × E => zxe.1.1) :=
    measurable_fst.comp measurable_fst
  have hx : Measurable (fun zxe : (LocalNuisance ι n × X) × E => zxe.1.2) :=
    measurable_snd.comp measurable_fst
  have hxe := hx.prodMk measurable_snd
  have hs' (i) := (hs i).comp hxe
  have hb' (i) := (hb i).comp hxe
  have hv' (γ) : Measurable (fun zxe : (LocalNuisance ι n × X) × E => vector zxe.2 γ) :=
    (hv γ).comp measurable_snd
  have ht' : Measurable (fun zxe : (LocalNuisance ι n × X) × E => time zxe.2) :=
    ht.comp measurable_snd
  have hw' (i) := (hw i).comp hx
  have hφ' (i γ) := (hφ i γ).comp hx
  unfold affineNuisanceIntegrand highResponseProduct
  apply Measurable.mul
  · apply (hact.comp measurable_snd).mul
    apply Finset.measurable_fun_prod
    intro i _
    exact (hs' i).mul ((measurable_pi_apply i).comp (measurable_fst.comp hz)) |>.add (hb' i)
  · apply Finset.measurable_fun_prod
    intro i _
    apply ternaryMass_measurable_both
    · unfold coefficientRegression coefficientReset
      fun_prop
    · fun_prop

theorem affineNuisanceNumerator_joint_measurable (π : Measure E) [SFinite π]
    (activation : E → ℝ) (hact : Measurable activation) (a η : ℝ)
    (slope intercept : E → X → Fin n → ℝ)
    (hs : ∀ i, Measurable (fun xe : X × E => slope xe.2 xe.1 i))
    (hb : ∀ i, Measurable (fun xe : X × E => intercept xe.2 xe.1 i))
    (vector : E → ι → ℝ) (hv : ∀ γ, Measurable (fun e => vector e γ))
    (time : E → ℝ) (ht : Measurable time)
    (w : X → Fin n → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (φ : X → Fin n → ι → ℝ) (hφ : ∀ i γ, Measurable (fun x => φ x i γ))
    (y : Fin n → Fin 3) :
    Measurable (fun zx : LocalNuisance ι n × X =>
      affineNuisanceNumerator π activation a η slope intercept vector time w φ zx.1 zx.2 y) := by
  have hI : Measurable (fun zx : LocalNuisance ι n × X => ∫ e,
      affineNuisanceIntegrand activation a η slope intercept vector time w φ zx.1 zx.2 y e ∂π) :=
    (affineNuisanceIntegrand_all_joint_measurable activation hact a η
      slope intercept hs hb vector hv time ht w hw φ hφ y).stronglyMeasurable.integral_prod_right'.measurable
  have hw' (i) : Measurable (fun zx : LocalNuisance ι n × X => w zx.2 i) :=
    (hw i).comp measurable_snd
  have hφ' (i γ) : Measurable (fun zx : LocalNuisance ι n × X => φ zx.2 i γ) :=
    (hφ i γ).comp measurable_snd
  unfold affineNuisanceNumerator
  apply hI.sub
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_fun_sum
    intro i _
    apply (hw' i).pow_const 2 |>.mul
    unfold highResponseVarianceTerm
    apply Measurable.const_mul
    apply Finset.measurable_fun_prod
    intro l _
    apply ternaryMass_measurable_both
    · unfold coefficientRegression
      fun_prop
    · fun_prop

end
end NearlyMinimax
