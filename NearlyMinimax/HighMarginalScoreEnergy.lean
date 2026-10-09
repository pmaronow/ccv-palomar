module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.PosteriorScoreEnergy


@[expose] public section

/-! Actual observed-data Fisher energy is bounded by genuine latent
append/heat likelihood Fisher energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem highMarginalRealScore_memLp_energy {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (hE : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      (highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2)^2 /
        highRawSampleLikelihood n a V (p z.1) (F z.1) z.2) (ν.prod (highSampleReference d n))) :
    let P := (highRealSampleKernel n a V p F hp hF) ∘ₘ
      (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)
    MemLp (highMarginalRealScore dependent hsymm ν π activation n a V η p F) 2 P ∧
      (∫ z, (highMarginalRealScore dependent hsymm ν π activation n a V η p F z)^2 ∂P) ≤
        (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
          ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
            (highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2)^2 /
              highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 ∂ν.prod (highSampleReference d n) := by
  let μ := highSampleReference d n
  let L : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun z =>
    highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
  let D : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun z =>
    highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
  let m := fun ω => highRawDensityMass (p ω)
  let G := massPowerNormalizer ν m n
  have hm := highRawDensityMass_joint_measurable p hp
  have hb (ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  have hG : 0 < G := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hLp (z) : 0 < L z := highRawSampleLikelihood_pos n a V p F
    (fun ω x => haRaw.trans_le (hraw ω x).1) hq z.1 z.2
  have hLb (z) : L z ≤ |bRaw|^n := (le_abs_self _).trans
    (highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) _ _ (hpb z.1) ha.ne'
      (fun x y => (hq z.1 x y).le) z.2)
  have hDb (z) : |D z| ≤ (Fintype.card J : ℝ) * (Ba * |bRaw|^n) +
      η^2 * (|bRaw|^n * ((n : ℝ)/a^2)) :=
    highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa habound
      n a V η |bRaw| (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2
  have he := posteriorMeanScore_memLp_energy ν μ L D
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF)
    (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF)
    hLp (|bRaw|^n) _ G hG hLb hDb hE
  have hden := highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha.ne'
    hraw (fun ω x y => (hq ω x y).le)
  let Pi := (highSampleIndexKernel n a V p F hp hF) ∘ₘ massPowerTilt ν m n
  have hpost : posteriorMeanScore ν L D = highMarginalIndexScore dependent hsymm ν π activation n a V η p F := rfl
  change MemLp (posteriorMeanScore ν L D) 2
      (μ.withDensity (fun z => ENNReal.ofReal ((∫ ω, L (ω,z) ∂ν) / G))) ∧ _ at he
  rw [hpost] at he
  change Pi = μ.withDensity (fun z => ENNReal.ofReal ((∫ ω, L (ω,z) ∂ν) / G)) at hden
  rw [← hden] at he
  have hmap : (highRealSampleKernel n a V p F hp hF) ∘ₘ massPowerTilt ν m n =
      Pi.map (encodeDesignResponse a) := by
    exact (Measure.map_comp _ _ (encodeDesignResponse_measurable a)).symm
  have hR := highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF
  have hcomp : (fun z => highMarginalRealScore dependent hsymm ν π activation n a V η p F
      (encodeDesignResponse a z)) = highMarginalIndexScore dependent hsymm ν π activation n a V η p F := by
    funext z
    exact congrArg (highMarginalIndexScore dependent hsymm ν π activation n a V η p F)
      (decodeDesignResponse_encode a ha z)
  dsimp only
  rw [hmap]
  constructor
  · apply (memLp_map_measure_iff hR.aestronglyMeasurable (encodeDesignResponse_measurable a).aemeasurable).2
    simpa only [Function.comp_def, hcomp] using he.1
  · rw [integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) (hR.pow_const 2).stronglyMeasurable]
    have hpoint (z) : highMarginalRealScore dependent hsymm ν π activation n a V η p F
        (encodeDesignResponse a z) = highMarginalIndexScore dependent hsymm ν π activation n a V η p F z :=
      congrFun hcomp z
    simp_rw [hpoint]
    exact he.2

end NearlyMinimax
