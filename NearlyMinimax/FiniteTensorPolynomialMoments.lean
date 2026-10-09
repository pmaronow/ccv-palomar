module

public import NearlyMinimax.GaussianPrimitiveSeparated
public import Mathlib.MeasureTheory.Integral.Pi


@[expose] public section

/-! Coefficient moment tensorization under actual finite product measures.
Only the primitive weighted coefficient pairs need to be integrable. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {σ E F : Type*} [DecidableEq σ] [MeasurableSpace E] [MeasurableSpace F]

def polynomialPairMoment (w : E → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : E) : ℝ := w e * (P e).coeff β * (P' e).coeff β'

theorem polynomialPairMoment_mul_expansion
    (w : E → ℝ) (v : F → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (Q Q' : F → MvPolynomial σ ℝ) (β β' : σ →₀ ℕ) (z : E × F) :
    polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      (fun z => P z.1 * Q z.2) (fun z => P' z.1 * Q' z.2) β β' z =
      ∑ b ∈ _root_.Finset.HasAntidiagonal.antidiagonal β,
        ∑ b' ∈ _root_.Finset.HasAntidiagonal.antidiagonal β',
        polynomialPairMoment w P P' b.1 b'.1 z.1 *
          polynomialPairMoment v Q Q' b.2 b'.2 z.2 := by
  unfold polynomialPairMoment
  rw [coeff_mul, coeff_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro b' hb'
  ring

theorem polynomialPairMoment_product_integrable
    (μ : Measure E) (ν : Measure F) [SigmaFinite μ] [SigmaFinite ν]
    (w : E → ℝ) (v : F → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (Q Q' : F → MvPolynomial σ ℝ)
    (hP : ∀ β β', Integrable (polynomialPairMoment w P P' β β') μ)
    (hQ : ∀ β β', Integrable (polynomialPairMoment v Q Q' β β') ν)
    (β β' : σ →₀ ℕ) :
    Integrable (polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      (fun z => P z.1 * Q z.2) (fun z => P' z.1 * Q' z.2) β β') (μ.prod ν) := by
  change Integrable (fun z : E × F => polynomialPairMoment
    (fun z : E × F => w z.1 * v z.2) (fun z => P z.1 * Q z.2)
    (fun z => P' z.1 * Q' z.2) β β' z) (μ.prod ν)
  simp_rw [polynomialPairMoment_mul_expansion]
  exact integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun b' _ =>
    (hP b.1 b'.1).mul_prod (hQ b.2 b'.2)

theorem polynomialPairMoment_product_integral
    (μ : Measure E) (ν : Measure F) [SigmaFinite μ] [SigmaFinite ν]
    (w : E → ℝ) (v : F → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (Q Q' : F → MvPolynomial σ ℝ)
    (hP : ∀ β β', Integrable (polynomialPairMoment w P P' β β') μ)
    (hQ : ∀ β β', Integrable (polynomialPairMoment v Q Q' β β') ν)
    (p p' q q' : MvPolynomial σ ℝ) (a b : ℝ)
    (hEP : ∀ β β', (∫ e, polynomialPairMoment w P P' β β' e ∂μ) =
      a * p.coeff β * p'.coeff β')
    (hEQ : ∀ β β', (∫ e, polynomialPairMoment v Q Q' β β' e ∂ν) =
      b * q.coeff β * q'.coeff β') (β β' : σ →₀ ℕ) :
    (∫ z, polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      (fun z => P z.1 * Q z.2) (fun z => P' z.1 * Q' z.2) β β' z ∂μ.prod ν) =
      (a * b) * (p * q).coeff β * (p' * q').coeff β' := by
  simp_rw [polynomialPairMoment_mul_expansion]
  rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ fun c' _ =>
    (hP c.1 c'.1).mul_prod (hQ c.2 c'.2))]
  simp_rw [integral_finsetSum _ (fun (c' : (σ →₀ ℕ) × (σ →₀ ℕ)) _ =>
    (hP _ c'.1).mul_prod (hQ _ c'.2)), integral_prod_mul, hEP, hEQ]
  rw [coeff_mul, coeff_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro c' hc'
  ring

def tensorPolynomialPairMoment {n : ℕ} (w : Fin n → E → ℝ)
    (P P' : Fin n → E → MvPolynomial σ ℝ) (β β' : σ →₀ ℕ)
    (e : Fin n → E) : ℝ :=
  (∏ j, w j (e j)) * (∏ j, P j (e j)).coeff β * (∏ j, P' j (e j)).coeff β'

theorem tensorPolynomialPairMoment_fin
    (μ : Measure E) [SigmaFinite μ] (n : ℕ)
    (w : Fin n → E → ℝ) (P P' : Fin n → E → MvPolynomial σ ℝ)
    (p p' : Fin n → MvPolynomial σ ℝ) (a : Fin n → ℝ)
    (hi : ∀ j β β', Integrable (polynomialPairMoment (w j) (P j) (P' j) β β') μ)
    (he : ∀ j β β', (∫ e, polynomialPairMoment (w j) (P j) (P' j) β β' e ∂μ) =
      a j * (p j).coeff β * (p' j).coeff β') :
    ∀ β β', Integrable (tensorPolynomialPairMoment w P P' β β') (Measure.pi (fun _ => μ)) ∧
      (∫ e, tensorPolynomialPairMoment w P P' β β' e ∂Measure.pi (fun _ => μ)) =
        (∏ j, a j) * (∏ j, p j).coeff β * (∏ j, p' j).coeff β' := by
  induction n with
  | zero =>
    intro β β'
    have hprob : IsProbabilityMeasure (Measure.pi (fun _ : Fin 0 => μ)) := by
      constructor
      rw [Measure.pi_empty_univ]
    let _ := hprob
    constructor
    · change Integrable (fun e : Fin 0 → E => tensorPolynomialPairMoment w P P' β β' e) _
      simp only [tensorPolynomialPairMoment, Finset.univ_eq_empty, Finset.prod_empty]
      exact integrable_const _
    · simp only [tensorPolynomialPairMoment, Finset.univ_eq_empty, Finset.prod_empty,
        integral_const, probReal_univ, one_smul]
  | succ n ih =>
    intro β β'
    let W (x : Fin n → E) := ∏ j, w j.succ (x j)
    let Q (x : Fin n → E) := ∏ j, P j.succ (x j)
    let Q' (x : Fin n → E) := ∏ j, P' j.succ (x j)
    have htail := ih (fun j => w j.succ) (fun j => P j.succ) (fun j => P' j.succ)
      (fun j => p j.succ) (fun j => p' j.succ) (fun j => a j.succ)
      (fun j => hi j.succ) (fun j => he j.succ)
    have hiTail : ∀ b b', Integrable (polynomialPairMoment W Q Q' b b')
        (Measure.pi (fun _ : Fin n => μ)) := fun b b' => (htail b b').1
    have heTail : ∀ b b', (∫ e, polynomialPairMoment W Q Q' b b' e
        ∂Measure.pi (fun _ : Fin n => μ)) =
        (∏ j : Fin n, a j.succ) * (∏ j : Fin n, p j.succ).coeff b *
          (∏ j : Fin n, p' j.succ).coeff b' := fun b b' => (htail b b').2
    let G := polynomialPairMoment (fun z : E × (Fin n → E) => w 0 z.1 * W z.2)
      (fun z => P 0 z.1 * Q z.2) (fun z => P' 0 z.1 * Q' z.2) β β'
    have hGi : Integrable G (μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
      polynomialPairMoment_product_integrable μ _ (w 0) W (P 0) (P' 0) Q Q'
        (hi 0) hiTail β β'
    have hGe : (∫ z, G z ∂μ.prod (Measure.pi (fun _ : Fin n => μ))) =
        (a 0 * ∏ j : Fin n, a j.succ) *
          (p 0 * ∏ j : Fin n, p j.succ).coeff β *
          (p' 0 * ∏ j : Fin n, p' j.succ).coeff β' :=
      polynomialPairMoment_product_integral μ _ (w 0) W (P 0) (P' 0) Q Q'
        (hi 0) hiTail (p 0) (p' 0) (∏ j : Fin n, p j.succ) (∏ j : Fin n, p' j.succ)
        (a 0) (∏ j : Fin n, a j.succ) (he 0) heTail β β'
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hcomp : (tensorPolynomialPairMoment w P P' β β') ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm = G := by
      funext z
      simp only [Function.comp_def, tensorPolynomialPairMoment,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove, G, W, Q, Q',
        polynomialPairMoment, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, cast_eq]
    constructor
    · rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      rw [hcomp]
      exact hGi
    · rw [← hmp.integral_comp']
      change (∫ x, ((tensorPolynomialPairMoment w P P' β β') ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm) x
        ∂μ.prod (Measure.pi (fun _ : Fin n => μ))) = _
      rw [hcomp, hGe]
      simp only [Fin.prod_univ_succ]

def tensorPolynomialPairMoment_fintype {κ : Type*} [Fintype κ]
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : κ → E) : ℝ :=
  (∏ j, w j (e j)) * (∏ j, P j (e j)).coeff β * (∏ j, P' j (e j)).coeff β'

theorem tensorPolynomialPairMoment_fintype_integral {κ : Type*} [Fintype κ]
    (μ : Measure E) [SigmaFinite μ]
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (p p' : κ → MvPolynomial σ ℝ) (a : κ → ℝ)
    (hi : ∀ j β β', Integrable (polynomialPairMoment (w j) (P j) (P' j) β β') μ)
    (he : ∀ j β β', (∫ e, polynomialPairMoment (w j) (P j) (P' j) β β' e ∂μ) =
      a j * (p j).coeff β * (p' j).coeff β') (β β' : σ →₀ ℕ) :
    Integrable (tensorPolynomialPairMoment_fintype w P P' β β') (Measure.pi (fun _ => μ)) ∧
      (∫ e, tensorPolynomialPairMoment_fintype w P P' β β' e ∂Measure.pi (fun _ => μ)) =
        (∏ j, a j) * (∏ j, p j).coeff β * (∏ j, p' j).coeff β' := by
  classical
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have h := tensorPolynomialPairMoment_fin μ (Fintype.card κ)
    (fun j => w (e j)) (fun j => P (e j)) (fun j => P' (e j))
    (fun j => p (e j)) (fun j => p' (e j)) (fun j => a (e j))
    (fun j => hi (e j)) (fun j => he (e j)) β β'
  have hmp := measurePreserving_piCongrLeft (fun _ : κ => μ) e
  have hcomp : (tensorPolynomialPairMoment_fintype w P P' β β') ∘
      MeasurableEquiv.piCongrLeft (fun _ : κ => E) e =
      tensorPolynomialPairMoment (fun j => w (e j)) (fun j => P (e j))
        (fun j => P' (e j)) β β' := by
    funext x
    simp only [Function.comp_def, tensorPolynomialPairMoment_fintype,
      tensorPolynomialPairMoment, ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply]
  constructor
  · rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp]
    exact h.1
  · rw [← hmp.integral_comp']
    change (∫ x, ((tensorPolynomialPairMoment_fintype w P P' β β') ∘
      MeasurableEquiv.piCongrLeft (fun _ : κ => E) e) x
      ∂Measure.pi (fun _ : Fin (Fintype.card κ) => μ)) = _
    rw [hcomp, h.2]
    simp only [e.prod_comp]

end NearlyMinimax
