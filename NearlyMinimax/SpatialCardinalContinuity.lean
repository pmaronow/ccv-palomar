module

public import NearlyMinimax.SpatialCardinalCovariance


@[expose] public section

noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-- Coefficients of any finite polynomial product vary continuously
when each factor coefficient does; the antidiagonal convolution is
finite and independent of the parameter. -/
theorem mvpolynomial_product_coefficients_continuous {α κ σ : Type*}
    [TopologicalSpace α] [DecidableEq σ] (s : Finset κ)
    (P : κ → α → MvPolynomial σ ℝ)
    (hP : ∀ k ∈ s, ∀ β, Continuous (fun x => (P k x).coeff β)) :
    ∀ β, Continuous (fun x => (∏ k ∈ s, P k x).coeff β) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro β; simp only [Finset.prod_empty]; exact continuous_const
  | @insert k s hk ih =>
    intro β
    simp only [Finset.prod_insert hk, coeff_mul]
    apply continuous_finsetSum
    intro w _
    exact (hP k (Finset.mem_insert_self _ _) w.1).mul
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) w.2)

theorem spatial_cardinal_affine_coefficients_continuous {d : ℕ} (β : Fin d →₀ ℕ) :
    Continuous (fun z : Covariate d × Covariate d => (spatialCardinalAffine z.1 z.2).coeff β) := by
  simp only [spatialCardinalAffine, coeff_sum, coeff_sub, coeff_C_mul]
  apply continuous_finsetSum
  intro r _
  apply Continuous.sub
  · by_cases hβ : (0 : Fin d →₀ ℕ) = β
    · simp only [coeff_C, hβ, ite_true]; fun_prop
    · simp only [coeff_C, hβ, ite_false]; exact continuous_const
  · exact (by fun_prop : Continuous (fun z : Covariate d × Covariate d => 8 * (z.2 r - z.1 r))).mul
      continuous_const

theorem spatial_cardinal_polynomial_coefficients_continuous {d n : ℕ}
    (i : Fin n) (β : Fin d →₀ ℕ) :
    Continuous (fun U : Fin n → Covariate d => (spatialCardinalPolynomial U i).coeff β) := by
  unfold spatialCardinalPolynomial
  have hcoeff (j : Fin n) (δ : Fin d →₀ ℕ) :
      Continuous (fun U : Fin n → Covariate d => (spatialCardinalAffine (U i) (U j)).coeff δ) := by
    simp only [spatialCardinalAffine, coeff_sum, coeff_sub, coeff_C_mul]
    apply continuous_finsetSum
    intro r _
    apply Continuous.sub
    · by_cases hδ : (0 : Fin d →₀ ℕ) = δ
      · simp only [coeff_C, hδ, ite_true]; fun_prop
      · simp only [coeff_C, hδ, ite_false]; exact continuous_const
    · exact (by fun_prop : Continuous (fun U : Fin n → Covariate d => 8 * (U j r - U i r))).mul
        continuous_const
  exact mvpolynomial_product_coefficients_continuous
    (α := Fin n → Covariate d) (κ := Fin n) (σ := Fin d)
    ((Finset.univ : Finset (Fin n)).erase i)
    (fun j (U : Fin n → Covariate d) => spatialCardinalAffine (U i) (U j))
    (fun j _ δ => hcoeff j δ) β

theorem spatial_squared_distance_continuous {d : ℕ} :
    Continuous (fun z : Covariate d × Covariate d => spatialSquaredDistance z.1 z.2) := by
  unfold spatialSquaredDistance
  fun_prop

theorem spatial_cardinal_matrix_continuous {d n D : ℕ} (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Continuous (fun z : (Fin n → ℝ) × (Fin n → Covariate d) =>
      spatialCardinalMatrix lam z.1 z.2 β β') := by
  unfold spatialCardinalMatrix
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul
  · apply Continuous.mul
    · unfold spatialCardinalScale spatialSquaredDistance
      fun_prop
    · exact (spatial_cardinal_polynomial_coefficients_continuous i
        (polynomialBoxExponent β.val)).comp continuous_snd
  · exact (spatial_cardinal_polynomial_coefficients_continuous i
      (polynomialBoxExponent β'.val)).comp continuous_snd


end NearlyMinimax
