module

public import NearlyMinimax.OrdinaryFineAliasAggregation
public import NearlyMinimax.AliasTailSummation


@[expose] public section

/-! The actual response-summed ordinary fine-alias factorial tail at the
paper's canonical rounded saddle. The fixed exp(L M) changes only the
factorial-tail constant and never the source activity exponent. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def ordinaryFineAliasSaddleCoefficient (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerSaddleCoefficient s d (densityIntervalExponent ad bd)

def ordinaryFineAliasSaddleTheta (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerSaddleTheta s d (densityIntervalExponent ad bd)

def ordinaryFineAliasSaddleTargetBound (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℕ :=
  lowerAliasFineTargetBound d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)

def ordinaryFineAliasSaddleTailPrefactor (s : ℝ) (d q : ℕ) (ad bd C a rho : ℝ) : ℝ :=
  ordinaryAliasFamilySpatialPrefactor d q (ordinaryFineAliasSaddleTargetBound s d ad bd)
    ad bd (densityIntervalExponent ad bd+1) C a rho

def ordinaryFineAliasSaddleTailExponent (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerAliasSpatialFixedL d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)

/-- Chosen once before the sample size, observation count, frame degree or
any nuisance tuple. -/
def ordinaryFineAliasFactorialConstant (s : ℝ) (d q : ℕ) (ad bd C a rho Csharp : ℝ) : ℝ :=
  aliasTailConstant (ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho)
    Csharp (ordinaryAliasSpatialResponseBase d bd) (ordinaryFineAliasSaddleTailExponent s d ad bd)

def ordinaryFineAliasSaddleResponseEnergy (s : ℝ) (d : ℕ) (ad bd Cw cf x : ℝ)
    (q : ℕ) (C a V : ℝ) (F : ℕ → ℕ)
    (p g w : (n : ℕ) → (Fin n → Covariate d) → Fin n → ℝ)
    (c : (n : ℕ) → (Fin n → Covariate d) → HighFrameIndex d (F n) → ℝ) (n : ℕ) : ℝ :=
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let L := lowerAliasCutoff s d m theta Cw (densityIntervalExponent ad bd+1) (shrunkDensityExponent ad bd) x
  let eta := lowerSaddleEta s d m theta Cw cf x
  ∑ y : Fin n → Fin 3, ∫ U,
    ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D L N mu)
      (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d) L
      (fun r => higherBandTargetScale d r N mu) M q C a V eta U
      (p n U) (g n U) (w n U) (c n U) y^2 ∂fullSpatialPatchDesign d n

/-- The genuine finite tail statement, uniform in count-varying frame
spaces and all tuple/count-varying nuisance values satisfying the raw
model legality guards. -/
def OrdinaryFineAliasFactorialTailProperty (s : ℝ) (d q : ℕ)
    (ad bd Cw cf C a rho Csharp x : ℝ) : Prop :=
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let eta := lowerSaddleEta s d m theta Cw cf x
  let C6 := ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp
  ∀ (V : ℝ) (F : ℕ → ℕ)
    (p g w : (n : ℕ) → (Fin n → Covariate d) → Fin n → ℝ)
    (c : (n : ℕ) → (Fin n → Covariate d) → HighFrameIndex d (F n) → ℝ),
    (∀ n, 1 ≤ n → ∀ i, Measurable (fun U => p n U i)) →
    (∀ n, 1 ≤ n → ∀ i, Measurable (fun U => g n U i)) →
    (∀ n, 1 ≤ n → ∀ i, Measurable (fun U => w n U i)) →
    (∀ n, 1 ≤ n → ∀ gamma, Measurable (fun U => c n U gamma)) →
    (∀ n, 1 ≤ n → ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i,
      p n U i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)) →
    (∀ n, 1 ≤ n → ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |g n U i| ≤ rho/2) →
    (∀ n, 1 ≤ n → ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |w n U i| ≤ 1) →
    (∀ n, 1 ≤ n → ∀ᵐ U ∂fullSpatialPatchDesign d n, ∑ gamma, |c n U gamma| ≤ C⁻¹) →
    (∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) →
    (∑ j ∈ Finset.range (D-M), poissonCountWeight (Csharp*mu) (M+1+j) *
      ordinaryFineAliasSaddleResponseEnergy s d ad bd Cw cf x q C a V F p g w c (M+1+j)) ≤
      C6 * (eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))) *
        poissonCountWeight (C6*mu) (M+1)

theorem ordinaryFineAliasFactorialConstant_ge_one {s ad bd C a rho Csharp : ℝ} {d q : ℕ}
    (hbd : 0 ≤ bd) (hCs : 0 ≤ Csharp) :
    1 ≤ ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp := by
  unfold ordinaryFineAliasFactorialConstant
  exact aliasTailConstant_ge_one (ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)
    hCs (by unfold ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity)

/-- Actual source-scale factorial aggregation. Every count energy is derived
from the genuine cardinal band and response action. The additional exp(LM)
is absorbed into the fixed C6, preserving exp(2tauM M). -/
theorem eventually_ordinaryFineAlias_factorial_tail {s ad bd : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4*s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd)
    (Cw cf : ℝ) (hcf : 0 ≤ cf) (q : ℕ) (C a rho Csharp : ℝ)
    (hC : 1 ≤ C) (ha : 0 < a) (hrho : 0 < rho) (hCs : 0 ≤ Csharp) :
    ∀ᶠ x in atTop, OrdinaryFineAliasFactorialTailProperty s d q ad bd Cw cf C a rho Csharp x := by
  let tau := densityIntervalExponent ad bd
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  have htau : 0 < tau := densityIntervalExponent_pos haD hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ)<d := by linarith
  have hmu := lowerSaddleMu_tends_zero hd0 hm htheta Cw
  have heta := lowerSaddleEta_tends_zero (by linarith : 0<s) hd0 hm htheta Cw cf
  have hd4 : 4 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by exact_mod_cast h
    omega
  filter_upwards [eventually_ordinaryFineAliasFamily_spatial_response_energy hs hd haD hab Cw q C a rho hC ha hrho.le,
    hmu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    heta.eventually (gt_mem_nhds (by linarith : (0 : ℝ)<rho/2)), eventually_gt_atTop (0 : ℝ)]
    with x henergy hmu1 hetaSmall hx
  unfold OrdinaryFineAliasFactorialTailProperty
  dsimp only
  intro V F p g w c hpmeas hgmeas hwmeas hcmeas hpD hg hw hc hp
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let eta := lowerSaddleEta s d m theta Cw cf x
  have hmu0 : 0 ≤ mu := by
    dsimp [mu]
    rw [lowerSaddleMu_eq_exp hx]
    positivity
  have heta0 : 0 ≤ eta := by
    unfold eta lowerSaddleEta lowerSaddleH
    positivity
  let A := ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho
  let L := ordinaryFineAliasSaddleTailExponent s d ad bd
  let B := ordinaryAliasSpatialResponseBase d bd
  let P := eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))
  have hA : 0 ≤ A := ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (mul_nonneg (pow_nonneg heta0 4) (Real.exp_pos _).le)
      (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _)
  have hB : 0 ≤ B := by unfold B ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity
  have hL : 0 ≤ L := lowerAliasSpatialFixedL_nonneg hd4 _ (by linarith)
  apply finite_alias_energy_tail_le hA hP hCs hB hL hmu0 hmu1.le M (D-M)
  intro j hj
  have hn : 1 ≤ M+1+j := by omega
  have he := henergy (M+1+j) (F (M+1+j)) hn V eta heta0 hetaSmall.le
    (p (M+1+j)) (g (M+1+j)) (w (M+1+j)) (c (M+1+j))
    (hpmeas _ hn) (hgmeas _ hn) (hwmeas _ hn) (hcmeas _ hn)
    (hpD _ hn) (hg _ hn) (hw _ hn) (hc _ hn) hp
  convert he using 1 <;>
    simp only [ordinaryFineAliasSaddleResponseEnergy, A, P, L, B, m, theta, M, D, N, mu, eta,
      ordinaryFineAliasSaddleTailPrefactor,
      ordinaryFineAliasSaddleTailExponent, ordinaryFineAliasSaddleTargetBound,
      ordinaryFineAliasSaddleCoefficient, ordinaryFineAliasSaddleTheta] <;> ring

/-- Natural sample sizes inherit the same fixed constant and actual rounded
scales; no new n-dependent constant is introduced. -/
theorem eventually_ordinaryFineAlias_factorial_tail_nat {s ad bd : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4*s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd)
    (Cw cf : ℝ) (hcf : 0 ≤ cf) (q : ℕ) (C a rho Csharp : ℝ)
    (hC : 1 ≤ C) (ha : 0 < a) (hrho : 0 < rho) (hCs : 0 ≤ Csharp) :
    ∀ᶠ n : ℕ in atTop, OrdinaryFineAliasFactorialTailProperty s d q ad bd Cw cf C a rho Csharp (n : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually
    (eventually_ordinaryFineAlias_factorial_tail hs hd haD hab Cw cf hcf q C a rho Csharp hC ha hrho hCs)

end NearlyMinimax
