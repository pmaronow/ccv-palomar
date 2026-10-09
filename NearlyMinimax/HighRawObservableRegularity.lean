module

public import NearlyMinimax.HighRawObservableDerivative
public import NearlyMinimax.HighObservableRegularity


@[expose] public section

/-! Closed-interval absolute continuity for the actual high-prior data observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem highRawObservable_lipschitzOn {d : ℕ} (n : ℕ) (a v η T P B : ℝ)
    (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) (ω : Ω) :
    LipschitzOnWith
      ⟨B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2))) * (highSampleReference d n).real Set.univ, by positivity⟩
      (fun u => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H) (Icc 0 T) := by
  let c : ℝ := B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2)))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let L : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z
  have hLM (u : ℝ) : Measurable (L u) := by
    have hj : Measurable (Function.uncurry (fun ω z =>
        highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z)) :=
      highRawSampleLikelihood_joint_measurable n a (v - η ^ 2 * u) p F hp hF
    have hw : Measurable (fun z => highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z) := hj.of_uncurry_left
    exact (hH.comp (encodeDesignResponse_measurable a)).mul hw
  have hi (u : ℝ) (hu : u ∈ Icc 0 T) : Integrable (L u) (highSampleReference d n) := by
    apply Integrable.of_bound (hLM u).aestronglyMeasurable (B * P ^ n)
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a (v - η ^ 2 * u) P hP
        (p ω) (F ω) (hpb ω) ha.ne' (hq u hu ω) z) (abs_nonneg _) hB
  have hl (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
      LipschitzOnWith ⟨c, hc⟩ (fun u => L u z) (Icc 0 T) := by
    apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun u _ => ((highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z).const_mul
        (H (encodeDesignResponse a z))).hasDerivWithinAt)
    intro u hu
    apply NNReal.coe_le_coe.1
    change ‖H (encodeDesignResponse a z) * (-η ^ 2 *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)‖ ≤ c
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul (hHb _) (mul_le_mul_of_nonneg_left
      (highRawSampleVarianceDerivative_abs_le n a (v - η ^ 2 * u) P ha hP
        (p ω) (F ω) (hpb ω) (hq u hu ω) z) (sq_nonneg η)) (by positivity) hB
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  change dist (∫ z, L u z ∂highSampleReference d n) (∫ z, L v z ∂highSampleReference d n) ≤
    c * (highSampleReference d n).real Set.univ * dist u v
  rw [dist_eq_norm, ← integral_sub (hi u hu) (hi v hv)]
  have hb : ∀ᵐ z ∂highSampleReference d n, ‖L u z - L v z‖ ≤ c * dist u v :=
    Eventually.of_forall fun z => by
      have he : dist (L u z) (L v z) ≤ c * dist u v := (hl z).dist_le_mul u hu v hv
      simpa only [dist_eq_norm] using he
  calc
    _ ≤ (c * dist u v) * (highSampleReference d n).real Set.univ := norm_integral_le_of_norm_le_const hb
    _ = _ := by ring

variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_rawObservable_exists_lipschitz (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    {d : ℕ} (n : ℕ) (a v η P B : ℝ) (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    ∃ K : NNReal, LipschitzOnWith K
      (fun u => ∫ ω, highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
        ∂historyMarkedPrior dependent Δ u π activation) (Icc 0 T) := by
  let G : ℝ → HistoryMarked dependent E → ℝ := fun u ω => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
  have hGM (u : ℝ) : Measurable (G u) := highRawObservable_measurable n a (v - η ^ 2 * u) p F hp hF H hH
  let M := B * P ^ n * (highSampleReference d n).real Set.univ
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hGb (u : ℝ) (hu : u ∈ Icc 0 T) (ω : HistoryMarked dependent E) : |G u ω| ≤ M :=
    highRawObservable_abs_le n a (v - η ^ 2 * u) P B hP hB (p ω) (F ω) (hpb ω) ha.ne' (hq u hu ω) H hHb
  let K : NNReal := ⟨B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2))) * (highSampleReference d n).real Set.univ, by positivity⟩
  have hGlip (ω : HistoryMarked dependent E) : LipschitzOnWith K (fun u => G u ω) (Icc 0 T) :=
    highRawObservable_lipschitzOn n a v η T P B ha hP hB p F hp hF hpb hq H hH hHb ω
  exact ⟨_, historyMarkedPrior_variable_observable_lipschitz dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation habound hsmall G hGM M hM hGb K hGlip⟩

end NearlyMinimax
