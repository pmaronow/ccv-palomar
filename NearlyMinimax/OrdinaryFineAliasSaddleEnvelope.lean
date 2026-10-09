module

public import NearlyMinimax.OrdinaryFineAliasGeometryEnvelope
public import NearlyMinimax.OrdinaryFineAliasFactorialTail


@[expose] public section

/-! Canonical rounded-saddle deterministic ordinary-alias envelope and its
actual spatial/factorial moments. No nuisance functions or chart inverses
occur in this universal geometry envelope. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def ordinaryFineAliasSaddleGeometryEnvelope (s : ℝ) (d q : ℕ)
    (ad bd Cw cf C a rho x : ℝ) (n F : ℕ) (U : Fin n → Covariate d) : ℝ :=
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  let c0 := densityIntervalExponent ad bd+1
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let L := lowerAliasCutoff s d m theta Cw c0 (shrunkDensityExponent ad bd) x
  let R := ordinaryFineAliasSaddleTargetBound s d ad bd
  let eta := lowerSaddleEta s d m theta Cw cf x
  ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) (ordinaryFineAliasTargetSet d D L N mu)
    M R q ad bd c0 C a rho eta L (fun r => higherBandTargetScale d r N mu) U

theorem ordinaryFineAliasSaddleGeometryEnvelope_nonneg (s : ℝ) (d q : ℕ)
    (ad bd Cw cf C a rho x : ℝ) (n F : ℕ) (U : Fin n → Covariate d) :
    0 ≤ ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F U :=
  ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ U

theorem ordinaryFineAliasSaddleGeometryEnvelope_measurable {s ad bd Cw x : ℝ} {d : ℕ}
    (G : OrdinaryFineAliasSaddleGuards s d ad bd Cw x)
    (q : ℕ) (cf C a rho : ℝ) (n F : ℕ) :
    Measurable (ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F) := by
  apply ordinaryFineAliasFamilyResponseSquareEnvelope_measurable
  · exact G.cutoff
  · intro r hr
    exact G.cutoff.trans (Finset.mem_filter.mp hr).2.2.le

/-- True universal Q^n envelope moment, at all counts and frame degrees.
The fixed constant is chosen before x, n, F or nuisance data. -/
theorem eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le
    {s ad bd : ℝ} {d : ℕ} (hs : 1 < s) (hd : 4*s < (d : ℝ))
    (haD : 0 < ad) (hab : ad < bd) (Cw cf : ℝ) (q : ℕ) (C a rho : ℝ) :
    ∀ᶠ x in atTop, ∀ (n F : ℕ),
      Integrable (ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F)
        (fullSpatialPatchDesign d n) ∧
      (∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F U
        ∂fullSpatialPatchDesign d n) ≤
        ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho *
          (lowerSaddleEta s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw cf x)^4 *
          Real.exp (2*shrunkDensityExponent ad bd
            (lowerSaddleM (ordinaryFineAliasSaddleCoefficient s d ad bd) x)*
            (lowerSaddleM (ordinaryFineAliasSaddleCoefficient s d ad bd) x)) *
          (lowerSaddleN s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw (shrunkDensityExponent ad bd) x)^(4-(d : ℝ)) *
          Real.exp (ordinaryFineAliasSaddleTailExponent s d ad bd*
            (lowerSaddleM (ordinaryFineAliasSaddleCoefficient s d ad bd) x)) *
          (ordinaryAliasSpatialResponseBase d bd)^n := by
  filter_upwards [eventually_ordinaryFineAlias_saddle_guards hs hd haD hab Cw] with x G
  intro n F
  have hLT : ∀ r ∈ ordinaryFineAliasTargetSet d
      (lowerSaddleD d (ordinaryFineAliasSaddleCoefficient s d ad bd) x)
      (lowerAliasCutoff s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
        (ordinaryFineAliasSaddleTheta s d ad bd) Cw (densityIntervalExponent ad bd+1) (shrunkDensityExponent ad bd) x)
      (lowerSaddleN s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
        (ordinaryFineAliasSaddleTheta s d ad bd) Cw (shrunkDensityExponent ad bd) x)
      (lowerSaddleMu d (ordinaryFineAliasSaddleCoefficient s d ad bd)
        (ordinaryFineAliasSaddleTheta s d ad bd) Cw x),
      lowerAliasCutoff s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
        (ordinaryFineAliasSaddleTheta s d ad bd) Cw (densityIntervalExponent ad bd+1) (shrunkDensityExponent ad bd) x ≤
      higherBandTargetScale d r
        (lowerSaddleN s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
          (ordinaryFineAliasSaddleTheta s d ad bd) Cw (shrunkDensityExponent ad bd) x)
        (lowerSaddleMu d (ordinaryFineAliasSaddleCoefficient s d ad bd)
          (ordinaryFineAliasSaddleTheta s d ad bd) Cw x) := fun r hr => (Finset.mem_filter.mp hr).2.2.le
  exact ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le G.dimension _ G.targets
    ad bd _ C a rho _ _ _ _ (haD.trans hab).le (Nat.cast_nonneg _) (by positivity)
    (by linarith [densityIntervalExponent_pos haD hab]) G.degree (lowerSaddleN_positive _ _ _ _ _ _ _)
    G.cutoff G.logarithm _ hLT q

/-- The deterministic geometry envelope has the actual factorial-tail
moment, at the paper's rounded M/D/N/mu and eta=cf*h^s. No nuisance or
conditional pointwise norm premise is needed. -/
theorem eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
    {s ad bd : ℝ} {d : ℕ} (hs : 1 < s) (hd : 4*s < (d : ℝ))
    (haD : 0 < ad) (hab : ad < bd) (Cw cf : ℝ) (q : ℕ)
    (C a rho Csharp : ℝ) (hCs : 0 ≤ Csharp) :
    ∀ᶠ x in atTop,
      let m := ordinaryFineAliasSaddleCoefficient s d ad bd
      let theta := ordinaryFineAliasSaddleTheta s d ad bd
      let M := lowerSaddleM m x
      let D := lowerSaddleD d m x
      let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
      let mu := lowerSaddleMu d m theta Cw x
      let eta := lowerSaddleEta s d m theta Cw cf x
      let C6 := ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp
      ∀ F : ℕ → ℕ,
        (∑ j ∈ Finset.range (D-M), poissonCountWeight (Csharp*mu) (M+1+j) *
          (∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x
            (M+1+j) (F (M+1+j)) U ∂fullSpatialPatchDesign d (M+1+j))) ≤
        C6 * (eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))) *
          poissonCountWeight (C6*mu) (M+1) := by
  let tau := densityIntervalExponent ad bd
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  have htau : 0 < tau := densityIntervalExponent_pos haD hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ)<d := by linarith
  have hd4 : 4 ≤ d := by
    have h : (4 : ℝ)<d := by linarith
    have h' : 4<d := by exact_mod_cast h
    omega
  filter_upwards [eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le hs hd haD hab Cw cf q C a rho,
    (lowerSaddleMu_tends_zero hd0 hm htheta Cw).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    eventually_gt_atTop (0 : ℝ)] with x henergy hmu1 hx
  dsimp only
  intro F
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let eta := lowerSaddleEta s d m theta Cw cf x
  let A := ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho
  let L := ordinaryFineAliasSaddleTailExponent s d ad bd
  let B := ordinaryAliasSpatialResponseBase d bd
  let P := eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))
  have hmu0 : 0 ≤ mu := by dsimp [mu]; rw [lowerSaddleMu_eq_exp hx]; positivity
  have hA : 0 ≤ A := ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _)
  have hB : 0 ≤ B := by unfold B ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity
  have hL : 0 ≤ L := lowerAliasSpatialFixedL_nonneg hd4 _ (by linarith)
  apply finite_alias_energy_tail_le hA hP hCs hB hL hmu0 hmu1.le M (D-M)
    (fun n => ∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x
      n (F n) U ∂fullSpatialPatchDesign d n)
  intro j hj
  have he := (henergy (M+1+j) (F (M+1+j))).2
  convert he using 1 <;> simp only [A,P,L,B,m,theta,M,D,N,mu,eta,
    ordinaryFineAliasSaddleTailPrefactor, ordinaryFineAliasSaddleTailExponent,
    ordinaryFineAliasSaddleTargetBound, ordinaryFineAliasSaddleCoefficient, ordinaryFineAliasSaddleTheta] <;> ring


/-- Exact canonical all-count fine-family raw expression, for physical-row
identification via HighSourceFineAliasIdentification. -/
def ordinaryFineAliasSaddleRawNumerator (s : ℝ) (d q : ℕ)
    (ad bd Cw cf C a V x : ℝ) (n F : ℕ) (U : Fin n → Covariate d)
    (p g w : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  let c0 := densityIntervalExponent ad bd+1
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let L := lowerAliasCutoff s d m theta Cw c0 (shrunkDensityExponent ad bd) x
  let eta := lowerSaddleEta s d m theta Cw cf x
  ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D L N mu)
    (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d) L
    (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y

/-- Canonical honest universal geometry domination. The density and response
nuisance values may be chosen independently for each response, with no
measurability or inverse-chart reconstruction requirement. -/
theorem ordinaryFineAliasSaddleGeometryEnvelope_dominates {s ad bd Cw x : ℝ} {d : ℕ}
    (G : OrdinaryFineAliasSaddleGuards s d ad bd Cw x) (haD : 0 < ad)
    (q : ℕ) (cf C a V rho : ℝ) (hcf : 0 ≤ cf) (hC : 1 ≤ C) (ha : 0 < a)
    (hrho : 0 ≤ rho) (n F : ℕ) (hn : 1 ≤ n)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : (Fin n → Fin 3) → Fin n → ℝ)
    (c : (Fin n → Fin 3) → HighFrameIndex d F → ℝ) :
    let M := lowerSaddleM (ordinaryFineAliasSaddleCoefficient s d ad bd) x
    let eta := lowerSaddleEta s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
      (ordinaryFineAliasSaddleTheta s d ad bd) Cw cf x
    eta ≤ rho/2 →
    (∀ y i, p y i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)) →
    (∀ y i, |g y i| ≤ rho/2) → (∀ y i, |w y i| ≤ 1) →
    (∀ y, ∑ gamma, |c y gamma| ≤ C⁻¹) →
    (∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) →
    (∑ y : Fin n → Fin 3, ordinaryFineAliasSaddleRawNumerator s d q ad bd Cw cf C a V x
      n F U (p y) (g y) (w y) (c y) y^2) ≤
      ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F U := by
  dsimp only
  intro hetarho hpD hg hw hc hp
  have heta0 : 0 ≤ lowerSaddleEta s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
      (ordinaryFineAliasSaddleTheta s d ad bd) Cw cf x := by
    unfold lowerSaddleEta lowerSaddleH
    positivity
  exact ordinaryFineAliasFamilyResponseSquareEnvelope_dominates _ ad bd _ _ _ haD
    G.shrunkInterval G.exponent (fun r hr => ⟨by have := (G.targets r hr).1; omega, (G.targets r hr).2⟩)
    q hn C a V _ rho hC ha heta0 hrho hetarho U hU p g w c hpD hg hw hc hp

end NearlyMinimax
