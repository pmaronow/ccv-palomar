module

public import NearlyMinimax.HigherGeometryEnergyAssembly
public import NearlyMinimax.CompleteGeometryExteriorEnergy


@[expose] public section

/-! Finite full-count energy assembly for the genuine spatial envelope.
The canonical statistical construction supplies the higher block from its
actual cardinal, ordinary alias, pair alias and field integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def completeGeometryDefectConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  1+|completeGeometryRadialConstant d B a rho Cs|+
    4*|cardinalGeometryFactorialConstant d q B C a rho Cs|

def completeGeometryFieldConstant (d q : ℕ) (aD bD C a rho c0 Cs : ℝ) : ℝ :=
  1+4*|finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)|

def completeGeometryAliasConstant (d q : ℕ) (aD bD C a rho c0 K Cs Cord : ℝ) : ℝ :=
  1+4*|Cord|+4*|finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)|

theorem completeGeometryDefectConstant_pos (d q : ℕ) (B C a rho Cs : ℝ) :
    0 < completeGeometryDefectConstant d q B C a rho Cs := by
  unfold completeGeometryDefectConstant
  positivity

theorem completeGeometryFieldConstant_pos (d q : ℕ) (aD bD C a rho c0 Cs : ℝ) :
    0 < completeGeometryFieldConstant d q aD bD C a rho c0 Cs := by
  unfold completeGeometryFieldConstant
  positivity

theorem completeGeometryAliasConstant_pos (d q : ℕ) (aD bD C a rho c0 K Cs Cord : ℝ) :
    0 < completeGeometryAliasConstant d q aD bD C a rho c0 K Cs Cord := by
  unfold completeGeometryAliasConstant
  positivity

theorem four_component_raw_energy_algebra {mu Pdef Pal Plo A2 Ad Ao Ap Af : ℝ}
    (hmu : 0 ≤ mu) (hPd : 0 ≤ Pdef) (hPal : 0 ≤ Pal) (hPlo : 0 ≤ Plo)
    (hPloPal : Plo ≤ Pal) (hAo : 0 ≤ Ao) (hAp : 0 ≤ Ap) (M : ℕ) :
    A2*Pdef+4*(Ad*Pdef+Ao*Pal*poissonCountWeight (Ao*mu) (M+1)+
      Ap*Plo*poissonCountWeight (Ap*mu) (M+1)+Af*Pdef) ≤
      3*((1+|A2|+4*|Ad|)+(1+4*|Af|))*Pdef+
      3*(1+4*|Ao|+4*|Ap|)*Pal*poissonCountWeight ((1+4*|Ao|+4*|Ap|)*mu) (M+1) := by
  let C6 := 1+4*|Ao|+4*|Ap|
  have hC6 : 0 ≤ C6 := by dsimp [C6]; positivity
  have hAoC : Ao ≤ C6 := by
    dsimp [C6]
    linarith only [le_abs_self Ao,abs_nonneg Ao,abs_nonneg Ap]
  have hApC : Ap ≤ C6 := by
    dsimp [C6]
    linarith only [le_abs_self Ap,abs_nonneg Ao,abs_nonneg Ap]
  have hoW := poissonCountWeight_mono (mul_nonneg hAo hmu)
    (mul_le_mul_of_nonneg_right hAoC hmu) (M+1)
  have hpW := poissonCountWeight_mono (mul_nonneg hAp hmu)
    (mul_le_mul_of_nonneg_right hApC hmu) (M+1)
  have ho := mul_le_mul_of_nonneg_left hoW (mul_nonneg hAo hPal)
  have hpP := mul_le_mul_of_nonneg_left hPloPal hAp
  have hp := mul_le_mul hpP hpW (poissonCountWeight_nonneg (mul_nonneg hAp hmu) _)
    (mul_nonneg hAp hPal)
  have hcoef : 4*(Ao+Ap) ≤ 3*C6 := by
    dsimp [C6]
    linarith only [le_abs_self Ao,le_abs_self Ap,abs_nonneg Ao,abs_nonneg Ap]
  have hAli := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg hPal (poissonCountWeight_nonneg (mul_nonneg hC6 hmu) (M+1)))
  have hDef : A2+4*Ad+4*Af ≤ 3*((1+|A2|+4*|Ad|)+(1+4*|Af|)) := by
    linarith only [le_abs_self A2,le_abs_self Ad,le_abs_self Af,
      abs_nonneg A2,abs_nonneg Ad,abs_nonneg Af]
  have hd := mul_le_mul_of_nonneg_right hDef hPd
  dsimp only [C6] at ho hp hAli hd
  nlinarith only [ho,hp,hAli,hd]

theorem completeSourceGeometryEnvelope_refined_integral {d : ℕ}
    (D M R q j : ℕ) (hj : 3+j ≤ D) (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) :
    (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl (3+j) U
      ∂fullSpatialPatchDesign d (3+j)) =
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3+j) := by
  have hcast : 3+j=j+3 := by omega
  rw [hcast] at hj ⊢
  simp only [completeSourceGeometryEnvelope,if_pos hj]

theorem completeSourceGeometryEnvelope_factorial_from_higher {d : ℕ} (hd : 0 < d)
    (D M R q n : ℕ) (hD : 3 ≤ D)
    (aD bD c0 K ell N mu C a rho eta Chi Bl Cs Cord tau : ℝ)
    (hN : 0 < N) (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hbd : 0 ≤ bD-(M : ℝ)⁻¹) (hbdB : bD-(M : ℝ)⁻¹ ≤ bD)
    (hCord : 0 ≤ Cord)
    (hCal : 0 ≤ finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs))
    (htau : 0 ≤ tau)
    (hhigher : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3+j)) ≤
      4*(cardinalGeometryFactorialConstant d q bD C a rho Cs*eta^4*N^(-(d : ℝ))*mu^2 +
        Cord*(eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))*poissonCountWeight (Cord*mu) (M+1) +
        finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs) *
          (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)*mu) (M+1) +
        finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ)))) :
    (∑ r ∈ Finset.range (n+1), poissonCountWeight (Cs*mu) r *
      ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl r U
        ∂fullSpatialPatchDesign d r) ≤
      3*(completeGeometryDefectConstant d q bD C a rho Cs+
        completeGeometryFieldConstant d q aD bD C a rho c0 Cs)*eta^4*mu^2*N^(-(d : ℝ)) +
      3*completeGeometryAliasConstant d q aD bD C a rho c0 K Cs Cord*eta^4*
        (Real.exp (2*tau*M)*N^(4-(d : ℝ)))*
          poissonCountWeight (completeGeometryAliasConstant d q aD bD C a rho c0 K Cs Cord*mu) (M+1) +
      Real.exp (completeGeometryExteriorConstant d Cs Chi)*eta^4*(Bl+1)^2*
        poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) (D+1) := by
  let e := fun r => ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl r U
    ∂fullSpatialPatchDesign d r
  have he (r : ℕ) : 0 ≤ e r := integral_nonneg
    (fun U => completeSourceGeometryEnvelope_nonneg D M R q aD bD c0 ell N mu C a rho eta Chi Bl r U)
  have he0 : e 0=0 := by simp [e,completeSourceGeometryEnvelope]
  have he1 : e 1=0 := by simp [e,completeSourceGeometryEnvelope]
  have hp := completeSourceGeometryEnvelope_pair_factorial_le D M R q aD bD c0 ell N mu C a rho eta Chi Bl Cs bD
    hd hN hCs hmu hbd hbdB
  have ht := completeSourceGeometryEnvelope_exterior_factorial_le (d := d) D M R q (n+1) (by omega)
    aD bD c0 ell N mu C a rho eta Chi Bl Cs hCs hmu hmu1
  have hh : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j)*e (3+j)) ≤
      4*(cardinalGeometryFactorialConstant d q bD C a rho Cs*eta^4*N^(-(d : ℝ))*mu^2 +
        Cord*(eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))*poissonCountWeight (Cord*mu) (M+1) +
        finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs) *
          (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)*mu) (M+1) +
        finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ))) := by
    apply le_trans (le_of_eq ?_) hhigher
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [e]
    rw [completeSourceGeometryEnvelope_refined_integral D M R q j (by
      have hj' := Finset.mem_range.mp hj
      omega)]
  have hblocks := finite_count_energy_from_blocks (mul_nonneg hCs hmu) n D (by omega)
    e he he0 he1 _ _ _ hp hh ht
  have hPloPal : eta^4*N^(4-(d : ℝ)) ≤ eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)) := by
    have heone : 1 ≤ Real.exp (2*tau*M) := Real.one_le_exp (by positivity)
    have h := mul_le_mul_of_nonneg_left heone (by positivity : 0 ≤ eta^4*N^(4-(d : ℝ)))
    convert h using 1 <;> ring
  have ha := four_component_raw_energy_algebra hmu
    (by positivity : 0 ≤ eta^4*mu^2*N^(-(d : ℝ)))
    (by positivity : 0 ≤ eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))
    (by positivity : 0 ≤ eta^4*N^(4-(d : ℝ))) hPloPal hCord hCal M
    (A2 := completeGeometryRadialConstant d bD a rho Cs)
    (Ad := cardinalGeometryFactorialConstant d q bD C a rho Cs)
    (Af := finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs))
  apply hblocks.trans
  have h := add_le_add_right ha
    (Real.exp (completeGeometryExteriorConstant d Cs Chi)*eta^4*(Bl+1)^2*
      poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) (D+1))
  convert h using 1 <;> (try dsimp [e,completeGeometryDefectConstant,completeGeometryFieldConstant,completeGeometryAliasConstant]) <;> ring

end NearlyMinimax
