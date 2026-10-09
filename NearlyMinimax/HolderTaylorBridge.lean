module

public import NearlyMinimax.CoordinatePartialBridge
public import RoughRegime.HolderTaylorApproximation


@[expose] public section

/-! Transport of the original open-domain Hölder model to genuine multivariate
Taylor polynomials. The two covariate representations have different norms;
the transport below retains the manuscript's Euclidean distance exactly. -/

noncomputable section
open Set
open scoped BigOperators ContDiff ENNReal

namespace NearlyMinimax

def euclideanCoordinates (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Covariate d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

def euclideanPoint {d : ℕ} (x : Covariate d) : EuclideanSpace ℝ (Fin d) :=
  (euclideanCoordinates d).symm x

def euclideanExtension {d : ℕ} (F : Covariate d → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  F ∘ euclideanCoordinates d

@[simp] theorem euclideanCoordinates_apply {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (i : Fin d) : euclideanCoordinates d x i = x i := rfl

@[simp] theorem euclideanPoint_apply {d : ℕ} (x : Covariate d) (i : Fin d) :
    euclideanPoint x i = x i := rfl

@[simp] theorem euclideanCoordinates_point {d : ℕ} (x : Covariate d) :
    euclideanCoordinates d (euclideanPoint x) = x :=
  (euclideanCoordinates d).apply_symm_apply x

theorem euclideanCoordinates_cube {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanCoordinates d x ∈ unitCube d ↔ x ∈ RoughRegime.Model.cube d := Iff.rfl

theorem euclideanPoint_cube {d : ℕ} (x : Covariate d) :
    euclideanPoint x ∈ RoughRegime.Model.cube d ↔ x ∈ unitCube d := Iff.rfl

theorem euclideanCoordinates_norm {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanNorm (euclideanCoordinates d x) = ‖x‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]
  simp only [euclideanCoordinates_apply, Real.norm_eq_abs, sq_abs]

theorem euclideanPoint_norm {d : ℕ} (x : Covariate d) :
    ‖euclideanPoint x‖ = euclideanNorm x := by
  rw [← euclideanCoordinates_norm, euclideanCoordinates_point]

theorem euclideanExtension_contDiffOn {d ℓ : ℕ} {U : Set (Covariate d)}
    {F : Covariate d → ℝ} (hf : ContDiffOn ℝ ℓ F U)
    (hcube : unitCube d ⊆ U) :
    ContDiffOn ℝ ℓ (euclideanExtension F) (RoughRegime.Model.cube d) := by
  apply (hf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap).mono
  intro x hx
  exact hcube hx

/-- Linear transport of the true ordered Fréchet derivative, with no norm
comparison and no differentiability assumption hidden in the coordinates. -/
theorem euclideanExtension_iteratedFDeriv {d q : ℕ} (F : Covariate d → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (σ : Fin q → Fin d) :
    iteratedFDeriv ℝ q (euclideanExtension F) x
        (fun j => EuclideanSpace.single (σ j) 1) =
      iteratedFDeriv ℝ q F (euclideanCoordinates d x)
        (fun j => Pi.single (σ j) 1) := by
  have he := (euclideanCoordinates d).iteratedFDerivWithin_comp_right
    F uniqueDiffOn_univ (x := x) (mem_univ _) q
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at he
  rw [show euclideanExtension F = F ∘ euclideanCoordinates d by rfl, he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe]
  congr 1

/-- Within-cube coordinate derivatives of the transported extension are the
true derivatives of the original function, including cube boundary points. -/
theorem euclideanExtension_coordinateDerivative {d ℓ q : ℕ}
    (U : Set (Covariate d)) (hU : IsOpen U) (F : Covariate d → ℝ)
    (hf : ContDiffOn ℝ ℓ F U) (hcube : unitCube d ⊆ U) (hq : q ≤ ℓ)
    (σ : Fin q → Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ RoughRegime.Model.cube d) :
    RoughRegime.Model.coordinateDerivative (euclideanExtension F) q σ x =
      iteratedFDeriv ℝ q F (euclideanCoordinates d x)
        (fun j => Pi.single (σ j) 1) := by
  have hqf : ContDiffOn ℝ q F U := hf.of_le (by exact_mod_cast hq)
  have hreg := hqf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap
  have hopen : IsOpen ((euclideanCoordinates d) ⁻¹' U) :=
    hU.preimage (euclideanCoordinates d).continuous
  have hxU : euclideanCoordinates d x ∈ U := hcube hx
  have hat : ContDiffAt ℝ q (euclideanExtension F) x :=
    hreg.contDiffAt (hopen.mem_nhds hxU)
  rw [RoughRegime.Model.coordinateDerivative_eq_iteratedFDeriv _ q σ x hx hat]
  exact euclideanExtension_iteratedFDeriv F x σ

/-- Pointwise ordered derivative bounds and the Euclidean top-order modulus
control the related library's closed-cube norm. This lemma is a transport
step; the original model supplies its two premises in the final bridge. -/
theorem euclideanExtension_mem_holderBall_of_coordinate_bounds {d : ℕ}
    (C : ModelConstants d) (F : Covariate d → ℝ)
    (hf : ContDiffOn ℝ C.order F C.domain)
    (hb : ∀ q ≤ C.order, ∀ σ : Fin q → Fin d, ∀ x ∈ C.domain,
      |iteratedFDeriv ℝ q F x (fun j => Pi.single (σ j) 1)| ≤ C.holderBound)
    (hm : ∀ σ : Fin C.order → Fin d, ∀ x ∈ C.domain, ∀ y ∈ C.domain,
      |iteratedFDeriv ℝ C.order F x (fun j => Pi.single (σ j) 1) -
        iteratedFDeriv ℝ C.order F y (fun j => Pi.single (σ j) 1)| ≤
          C.holderBound * euclideanNorm (x - y) ^ C.alpha) :
    euclideanExtension F ∈ RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound) := by
  have horder : RoughRegime.Model.holderOrder C.smoothness = C.order := C.order_eq.symm
  have halpha : RoughRegime.Model.holderExponent C.smoothness = C.alpha := by
    simp only [RoughRegime.Model.holderExponent, horder, ModelConstants.alpha]
  have hreg : ContDiffOn ℝ (RoughRegime.Model.holderOrder C.smoothness)
      (euclideanExtension F) (RoughRegime.Model.cube d) := by
    rw [horder]
    exact euclideanExtension_contDiffOn hf C.cube_subset
  have hsup : RoughRegime.Model.derivativeSup (euclideanExtension F)
      (RoughRegime.Model.holderOrder C.smoothness) ≤ ENNReal.ofReal C.holderBound := by
    unfold RoughRegime.Model.derivativeSup
    rw [horder]
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    rw [euclideanExtension_coordinateDerivative C.domain C.domain_open F hf
      C.cube_subset hq σ x hx]
    exact ENNReal.ofReal_le_ofReal (hb q hq σ _ (C.cube_subset hx))
  have hsem : RoughRegime.Model.holderSeminorm (euclideanExtension F) C.smoothness ≤
      ENNReal.ofReal C.holderBound := by
    unfold RoughRegime.Model.holderSeminorm
    rw [horder, halpha]
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    apply ENNReal.ofReal_le_ofReal
    have hmod := hm σ _ (C.cube_subset hx) _ (C.cube_subset hy)
    change |iteratedFDeriv ℝ C.order F (euclideanCoordinates d x)
        (fun j => Pi.single (σ j) 1) -
      iteratedFDeriv ℝ C.order F (euclideanCoordinates d y)
        (fun j => Pi.single (σ j) 1)| ≤
      C.holderBound * euclideanNorm (euclideanCoordinates d x - euclideanCoordinates d y) ^
        C.alpha at hmod
    rw [euclideanExtension_coordinateDerivative C.domain C.domain_open F hf
      C.cube_subset le_rfl σ x hx,
      euclideanExtension_coordinateDerivative C.domain C.domain_open F hf
      C.cube_subset le_rfl σ y hy]
    have hnorm : euclideanNorm (euclideanCoordinates d x - euclideanCoordinates d y) =
        ‖x - y‖ := by rw [← map_sub, euclideanCoordinates_norm]
    rw [hnorm] at hmod
    exact (div_le_iff₀ (Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).2 hmod
  change RoughRegime.Model.holderNorm (euclideanExtension F) C.smoothness ≤ _
  unfold RoughRegime.Model.holderNorm
  rw [if_pos ⟨C.smoothness_pos, hreg⟩]
  calc
    _ ≤ ENNReal.ofReal C.holderBound + ENNReal.ofReal C.holderBound := add_le_add hsup hsem
    _ = ENNReal.ofReal (2 * C.holderBound) := by
      rw [← ENNReal.ofReal_add C.holderBound_pos.le C.holderBound_pos.le]
      congr 1
      ring

/-- The manuscript's actual open-domain sum norm implies the related
ordered-coordinate closed-cube norm, with the explicit harmless factor two. -/
theorem euclideanExtension_mem_holderBall {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ) (hf : ContDiffOn ℝ C.order F C.domain)
    (hNorm : holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound) :
    euclideanExtension F ∈ RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound) := by
  apply euclideanExtension_mem_holderBall_of_coordinate_bounds C F hf
  · intro q hq σ x hx
    exact ordered_coordinate_bound C.domain C.domain_open F C.order C.alpha C.holderBound
      C.holderBound_pos.le hf hNorm q hq σ x hx
  · intro σ x hx y hy
    exact ordered_coordinate_modulus C.domain C.domain_open F C.order C.alpha C.holderBound
      C.holderBound_pos.le hf hNorm σ x y hx hy

/-- Concrete polynomial in the original covariates, obtained from the true
multivariate Taylor coefficients after the Euclidean coordinate transport. -/
def modelTaylorPolynomial {d : ℕ} (C : ModelConstants d) (F : Covariate d → ℝ)
    (x : Covariate d) : MvPolynomial (Fin d) ℝ :=
  RoughRegime.Model.holderTaylorPolynomial (euclideanExtension F) C.order (euclideanPoint x)

theorem modelTaylorPolynomial_degree {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ) (x : Covariate d) :
    (modelTaylorPolynomial C F x).totalDegree ≤ C.order :=
  RoughRegime.Model.holderTaylorPolynomial_degree _ _ _

/-- Taylor approximation from the transported regularity. The final model
bridge establishes membership from the original sum of mixed partial norms. -/
theorem modelTaylorPolynomial_error_of_holderBall {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ)
    (hf : euclideanExtension F ∈
      RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound))
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) :
    |F y - MvPolynomial.eval y (modelTaylorPolynomial C F x)| ≤
      ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
        euclideanNorm (y - x) ^ C.smoothness := by
  have herr := RoughRegime.Model.holderTaylorPolynomial_error (euclideanExtension F)
    C.smoothness (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le) hf
    (euclideanPoint x) (euclideanPoint y) hx hy
  have horder : RoughRegime.Model.holderOrder C.smoothness = C.order := C.order_eq.symm
  rw [horder] at herr
  have hdiff : euclideanPoint y - euclideanPoint x = euclideanPoint (y - x) :=
    ((euclideanCoordinates d).symm.map_sub y x).symm
  rw [hdiff, euclideanPoint_norm] at herr
  simpa only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point,
    euclideanPoint_apply, modelTaylorPolynomial] using herr

/-- The original model's regularity gives the genuine multivariate Taylor
remainder uniformly on the design cube, in every finite smoothness order. -/
theorem modelTaylorPolynomial_error {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ) (hf : ContDiffOn ℝ C.order F C.domain)
    (hNorm : holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound)
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) :
    |F y - MvPolynomial.eval y (modelTaylorPolynomial C F x)| ≤
      ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
        euclideanNorm (y - x) ^ C.smoothness :=
  modelTaylorPolynomial_error_of_holderBall C F
    (euclideanExtension_mem_holderBall C F hf hNorm) x y hx hy

/-- The approximation factor depends only on dimension and smoothness order,
and retains the norm radius as a separate multiplicative factor. -/
def taylorErrorFactor {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 * (d : ℝ) ^ C.order / C.order.factorial) *
    (Real.sqrt (d : ℝ)) ^ C.smoothness

theorem taylorErrorFactor_pos {d : ℕ} (C : ModelConstants d) :
    0 < taylorErrorFactor C := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast C.dimension_pos
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd
  unfold taylorErrorFactor
  exact mul_pos (div_pos (mul_pos (by norm_num) (pow_pos hd _))
    (by exact_mod_cast Nat.factorial_pos _)) (Real.rpow_pos_of_pos hs _)

theorem modelTaylorPolynomial_cell_error_of_holderBall {d : ℕ}
    (C : ModelConstants d) (F : Covariate d → ℝ)
    (hf : euclideanExtension F ∈
      RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound))
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (h : ℝ) (hh : 0 ≤ h) (hxy : ∀ i, |y i - x i| ≤ h) :
    |F y - MvPolynomial.eval y (modelTaylorPolynomial C F x)| ≤
      taylorErrorFactor C * C.holderBound * h ^ C.smoothness := by
  have he := modelTaylorPolynomial_error_of_holderBall C F hf x y hx hy
  have hr := euclideanNorm_le_coordinate_radius (y - x) h hh hxy
  have hp := Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hr C.smoothness_pos.le
  have hcoef : 0 ≤ (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial := by
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _)
      (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  calc
    _ ≤ ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
        euclideanNorm (y - x) ^ C.smoothness := he
    _ ≤ ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
        (Real.sqrt (d : ℝ) * h) ^ C.smoothness := mul_le_mul_of_nonneg_left hp hcoef
    _ = _ := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) hh]
      unfold taylorErrorFactor
      ring

theorem modelTaylorPolynomial_cell_error {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ) (hf : ContDiffOn ℝ C.order F C.domain)
    (hNorm : holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound)
    (x y : Covariate d) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (h : ℝ) (hh : 0 ≤ h) (hxy : ∀ i, |y i - x i| ≤ h) :
    |F y - MvPolynomial.eval y (modelTaylorPolynomial C F x)| ≤
      taylorErrorFactor C * C.holderBound * h ^ C.smoothness :=
  modelTaylorPolynomial_cell_error_of_holderBall C F
    (euclideanExtension_mem_holderBall C F hf hNorm) x y hx hy h hh hxy

/-- Every admissible regression admits a degree-bounded Taylor polynomial
around each point in the design cube, with the original Hölder radius. -/
theorem admissible_regression_taylor {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ C.order ∧
      ∀ y ∈ unitCube d, |θ.regression y - MvPolynomial.eval y P| ≤
        ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
          euclideanNorm (y - x) ^ C.smoothness := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  refine ⟨modelTaylorPolynomial C F x, modelTaylorPolynomial_degree C F x, ?_⟩
  intro y hy
  simpa only [hcube y hy] using modelTaylorPolynomial_error C F hreg hNorm x y hx hy

/-- Uniform polynomial approximation on a cell of side `h`. The explicit
error factor depends only on dimension and smoothness, not the open domain. -/
theorem admissible_regression_taylor_cell {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (x : Covariate d) (hx : x ∈ unitCube d) (h : ℝ) (hh : 0 ≤ h) :
    ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ C.order ∧
      ∀ y ∈ unitCube d, (∀ i, |y i - x i| ≤ h) →
        |θ.regression y - MvPolynomial.eval y P| ≤
          taylorErrorFactor C * C.holderBound * h ^ C.smoothness := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  refine ⟨modelTaylorPolynomial C F x, modelTaylorPolynomial_degree C F x, ?_⟩
  intro y hy hxy
  simpa only [hcube y hy] using
    modelTaylorPolynomial_cell_error C F hreg hNorm x y hx hy h hh hxy

end NearlyMinimax
