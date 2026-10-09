module

public import NearlyMinimax.HighDensityUpdates
public import NearlyMinimax.HighResponseUpdates


@[expose] public section

/-! The local row identity for arbitrary finite positive separated
representations, derived from the genuine density and response marks. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section ResponseIntegral
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fixed coefficients of the response action as a linear map of A. -/
def responseMatrixEntryCoefficient (q : ℕ) (C : ℝ) (c : ι → ℝ)
    (Φ : (ι → ℝ) → ℝ) (i j : ι) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, (C ^ 2 / 2 * fairSign s * fairSign t) *
    ∑ h : Fin (2 * q + 2), responseWeight q h *
      Φ (coefficientReset c (covarianceAtom C i j s t) (responseNode q h))

theorem responseMatrixAction_entry_sum (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C A c Φ =
      ∑ i, ∑ j, A i j * responseMatrixEntryCoefficient q C c Φ i j := by
  simp only [responseMatrixAction, covarianceAction, covarianceWeight,
    responseMatrixEntryCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem responseMatrixAction_scalar_matrix (q : ℕ) (C t : ℝ)
    (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => t * A i j) c Φ =
      t * responseMatrixAction q C A c Φ := by
  simp only [responseMatrixAction_entry_sum, Finset.mul_sum, mul_assoc]

variable {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)

theorem responseMatrixAction_measurable (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    Measurable (fun ζ => responseMatrixAction q C (A ζ) c Φ) := by
  simp only [responseMatrixAction_entry_sum]
  exact Finset.measurable_fun_sum _ (fun i _ => Finset.measurable_fun_sum _
    (fun j _ => (hA i j).mul_const _))

theorem responseMatrixAction_integrable (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    Integrable (fun ζ => responseMatrixAction q C (A ζ) c Φ) σ := by
  simp only [responseMatrixAction_entry_sum]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (hA i j).mul_const _))

/-- The actual fixed-atom response rule commutes with the positive
representation integral by its proved matrix linearity. -/
theorem responseMatrixAction_integral (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => ∫ ζ, A ζ i j ∂σ) c Φ =
      ∫ ζ, responseMatrixAction q C (A ζ) c Φ ∂σ := by
  simp only [responseMatrixAction_entry_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum _
    (fun j _ => (hA i j).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => (hA i j).mul_const _)]
  simp only [integral_mul_const]

end ResponseIntegral

section Separated
variable {Z α : Type*} [MeasurableSpace Z] [DecidableEq α]

theorem densitySeparatedSym_measurable (r : ℕ) (B : Z → α → Fin r → ℝ)
    (hB : ∀ i l, Measurable (fun ζ => B ζ i l)) (S : Finset α) (hS : S.card = r) :
    Measurable (fun ζ => densitySeparatedSym r (B ζ) S) := by
  classical
  let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa using hS)).symm
  have he : (fun ζ => densitySeparatedSym r (B ζ) S) =
      (fun ζ => (∑ τ : Equiv.Perm (Fin r), ∏ i, B ζ (e i) (τ i)) / (r.factorial : ℝ)) := by
    funext ζ
    exact densitySeparatedSym_eq_permutation_average r (B ζ) S e
  rw [he]
  exact (Finset.measurable_fun_sum _ (fun τ _ => Finset.measurable_fun_prod _
    (fun i _ => hB (e i) (τ i)))).div_const _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def separatedMatrixCost (A : Z → ι → ι → ℝ) (ζ : Z) : ℝ := ∑ i, ∑ j, |A ζ i j|

theorem separatedMatrixCost_entry_le (A : Z → ι → ι → ℝ) (ζ : Z) (i j : ι) :
    |A ζ i j| ≤ separatedMatrixCost A ζ := by
  apply (Finset.single_le_sum (fun k _ => abs_nonneg (A ζ i k)) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (A ζ k l)))
    (Finset.mem_univ i)

theorem separatedMatrix_entry_integrable (σ : Measure Z) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (i j : ι) :
    Integrable (fun ζ => A ζ i j) σ := by
  apply hcost.mono' (hA i j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ζ => by
    simpa only [Real.norm_eq_abs] using separatedMatrixCost_entry_le A ζ i j)

/-- Actual separated representation of the symmetric matrix kernel on a
cardinality-r observation subset. -/
def separatedSubsetMatrix (σ : Measure Z) (r : ℕ) (B : Z → α → Fin r → ℝ)
    (A : Z → ι → ι → ℝ) (S : Finset α) : ι → ι → ℝ :=
  fun i j => ∫ ζ, densitySeparatedSym r (B ζ) S * A ζ i j ∂σ

theorem separated_subset_entry_integrable (σ : Measure Z) (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (S : Finset α) (hS : S.card = r) (i j : ι) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * A ζ i j) σ := by
  apply hcost.mono' ((densitySeparatedSym_measurable r B hB S hS).mul (hA i j)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ζ
  change ‖densitySeparatedSym r (B ζ) S * A ζ i j‖ ≤ separatedMatrixCost A ζ
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ 1 * |A ζ i j| := mul_le_mul_of_nonneg_right
      (densitySeparatedSym_abs_le_one r (B ζ) S hS (fun i _ l => hBbound ζ i l)) (abs_nonneg _)
    _ ≤ separatedMatrixCost A ζ := by simpa using separatedMatrixCost_entry_le A ζ i j

theorem separatedSubsetMatrix_response (σ : Measure Z) (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (S : Finset α) (hS : S.card = r)
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (separatedSubsetMatrix σ r B A S) c Φ =
      ∫ ζ, densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  unfold separatedSubsetMatrix
  rw [responseMatrixAction_integral σ q C _
    (separated_subset_entry_integrable σ r B hB hBbound A hA hcost S hS)]
  simp only [responseMatrixAction_scalar_matrix]

theorem densityDerivativeAction_mul_right (r D : ℕ) (f : (Fin r → ℝ) → ℝ) (t : ℝ) :
    densityDerivativeAction r D (fun ε => f ε * t) = densityDerivativeAction r D f * t := by
  simp only [densityDerivativeAction, Finset.sum_mul, mul_assoc]

theorem densityPacketAction_mul_right (a b : ℝ) (m r D : ℕ)
    (f : ℝ → (Fin r → ℝ) → ℝ) (t : ℝ) :
    densityPacketAction a b m r D (fun z ε => f z ε * t) = densityPacketAction a b m r D f * t := by
  simp only [densityPacketAction, densityDerivativeAction_mul_right, Finset.sum_mul, mul_assoc]

theorem densityPacketAction_zero (a b : ℝ) (m r D : ℕ) :
    densityPacketAction a b m r D (fun _ _ => 0) = 0 := by
  simp [densityPacketAction, densityDerivativeAction]

/-- The genuine iterated action of the density packet, representation
measure, and finite response covariance rule. -/
def highSeparatedPacketAction (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∫ ζ, densityPacketAction a b m r D
    (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) ∂σ

theorem highSeparatedPacketAction_annihilates_constants (σ : Measure Z)
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c G (fun _ => 1) = 0 := by
  simp only [highSeparatedPacketAction, responseMatrixAction_zero_mass, mul_zero,
    densityPacketAction_zero, integral_zero]

theorem highSeparatedPacketAction_annihilates_coordinates (σ : Measure Z)
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (i : ι) :
    highSeparatedPacketAction σ a b m r D q C A c G (fun v => v i) = 0 := by
  simp only [highSeparatedPacketAction, responseMatrixAction_zero_mean, mul_zero,
    densityPacketAction_zero, integral_zero]

theorem separated_subset_response_integrable (σ : Measure Z) (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (S : Finset α) (hS : S.card = r)
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ) σ := by
  have h := responseMatrixAction_integrable σ q C
    (fun ζ i j => densitySeparatedSym r (B ζ) S * A ζ i j)
    (separated_subset_entry_integrable σ r B hB hBbound A hA hcost S hS) c Φ
  simpa only [responseMatrixAction_scalar_matrix] using h

/-- The paper's local row formula for arbitrary positive separated
representations. All integrability needed to commute sums and integrals
is derived from the finite representation cost. -/
theorem highSeparatedPacketAction_row (σ : Measure Z) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ := by
  have hInt (U : Finset α) (hU : U ∈ S.powersetCard r) :
      Integrable (fun ζ => (∏ i ∈ U, p i) *
        (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ)) σ :=
    (separated_subset_response_integrable σ r B hB hBbound A hA hcost U
      (Finset.mem_powersetCard.mp hU).2 q C c Φ).const_mul _
  have he (ζ : Z) : densityPacketAction a b m r D
      (fun z ε => (∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) *
        responseMatrixAction q C (A ζ) c Φ) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ) := by
    rw [densityPacketAction_mul_right,
      density_packet_product_exact S a b ha hab m r D hr hD hSD p (B ζ)]
    simp only [Finset.sum_mul, mul_assoc]
  unfold highSeparatedPacketAction
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ hInt]
  apply congrArg (fun t => densityCountCoefficient a b m r S.card * t)
  apply Finset.sum_congr rfl
  intro U hU
  rw [integral_const_mul, ← separatedSubsetMatrix_response σ r B hB hBbound A hA hcost U
    (Finset.mem_powersetCard.mp hU).2 q C c Φ]

theorem highSeparatedPacketAction_count_selector (σ : Measure Z) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D) (hSm : S.card ≤ m) (hrS : r ≤ S.card) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ else 0 := by
  rw [highSeparatedPacketAction_row σ a b ha hab m r D q hr hD S hSD p B hB hBbound C A hA hcost c Φ,
    densityCountCoefficient_exact a b ha hab m r S.card hr hrS hSm]
  split_ifs <;> simp

end Separated
end NearlyMinimax
