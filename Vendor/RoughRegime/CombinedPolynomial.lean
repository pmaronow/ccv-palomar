module

public import RoughRegime.MatrixDeterminant


@[expose] public section

/-! The exact entry polynomials for the matrix-inverse/determinant product in
Lemma 5(a), with all matrix entries represented as independent variables. -/

noncomputable section
open scoped BigOperators

namespace RoughRegime.CombinedPolynomial

open MatrixDeterminant MatrixUpper Upper

abbrev Variables {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) :=
  (Fin n0 × Fin n0) ⊕ ((i : Fin N) × (Fin (dims i) × Fin (dims i)))

def inverseVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin n0 × Fin n0 => (Sum.inl ab : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi a b)

def determinantVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin (dims i) × Fin (dims i) => (Sum.inr ⟨i, ab⟩ : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi (n := Fin (dims i))).det

def combinedVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  inverseVariableSeries n0 dims lo hi a b * ∏ i, determinantVariableSeries n0 dims lo hi i

def combinedCoefficientPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  PowerSeries.coeff k (combinedVariableSeries n0 dims lo hi a b)

lemma inverseVariableSeries_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) :
    (PowerSeries.coeff k (inverseVariableSeries n0 dims lo hi a b)).totalDegree ≤ k := by
  rw [inverseVariableSeries, PowerSeries.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  simp only [variableKernelSeries, PowerSeries.coeff_mk]
  exact (matrixEntryPolynomial_degree _ a b).trans (kernelCoefficientPolynomial_natDegree lo hi k)

lemma determinantVariableSeries_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) (k : ℕ) :
    (PowerSeries.coeff k (determinantVariableSeries n0 dims lo hi i)).totalDegree ≤ k := by
  rw [determinantVariableSeries, PowerSeries.coeff_map]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (determinantCoefficientPolynomial_totalDegree lo hi k)

theorem combinedCoefficientPolynomial_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) :
    (combinedCoefficientPolynomial n0 dims lo hi a b k).totalDegree ≤ k := by
  apply coeff_totalDegree_mul_le
  · exact inverseVariableSeries_degree n0 dims lo hi a b
  · intro j
    exact coeff_totalDegree_prod_le Finset.univ _
      (fun i _ => determinantVariableSeries_degree n0 dims lo hi i) j

def truncationEntryPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  MvPolynomial.C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹) *
    ∑ k ∈ Finset.range (m + 1), combinedCoefficientPolynomial n0 dims lo hi a b k

theorem truncationEntryPolynomial_degree {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) :
    (truncationEntryPolynomial n0 dims lo hi a b m).totalDegree ≤ m := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  exact (combinedCoefficientPolynomial_degree n0 dims lo hi a b k).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

def entryValuation {N : ℕ} {n0 : ℕ} {dims : Fin N → ℕ}
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) : Variables n0 dims → ℝ
  | Sum.inl ab => M0 ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2

lemma eval_renamed_series {V W : Type*} (f : V → W) (values : W → ℝ)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (values ∘ f)) P := by
  ext k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  change MvPolynomial.eval values (MvPolynomial.rename f (PowerSeries.coeff k P)) = _
  exact MvPolynomial.eval_rename f values _

lemma inverseVariableSeries_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (a b : Fin n0) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
      (inverseVariableSeries n0 dims lo hi a b) = kernelSeries lo hi M0 a b := by
  rw [inverseVariableSeries, eval_renamed_series]
  exact congrArg (fun A => A a b) (variableKernelSeries_map_eval lo hi M0)

lemma determinantVariableSeries_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (i : Fin N) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
      (determinantVariableSeries n0 dims lo hi i) = (kernelSeries lo hi (M i)).det := by
  rw [determinantVariableSeries, eval_renamed_series]
  ext k
  rw [PowerSeries.coeff_map]
  exact determinantCoefficientPolynomial_eval lo hi (M i) k

theorem combinedVariableSeries_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (a b : Fin n0) :
    PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation M0 M))
      (combinedVariableSeries n0 dims lo hi a b) =
      kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det := by
  simp only [combinedVariableSeries, map_mul, map_prod,
    inverseVariableSeries_eval, determinantVariableSeries_eval]

theorem combinedCoefficientPolynomial_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (a b : Fin n0) (k : ℕ) :
    MvPolynomial.eval (entryValuation M0 M)
      (combinedCoefficientPolynomial n0 dims lo hi a b k) =
      PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) := by
  have he := congrArg (fun P : PowerSeries ℝ => PowerSeries.coeff k P)
    (combinedVariableSeries_eval n0 dims lo hi M0 M a b)
  rw [PowerSeries.coeff_map] at he
  exact he

theorem truncationEntryPolynomial_eval {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (a b : Fin n0) (m : ℕ) :
    MvPolynomial.eval (entryValuation M0 M) (truncationEntryPolynomial n0 dims lo hi a b m) =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (kernelSeries lo hi M0 a b * ∏ i, (kernelSeries lo hi (M i)).det) := by
  simp [truncationEntryPolynomial, combinedCoefficientPolynomial_eval]

end RoughRegime.CombinedPolynomial
