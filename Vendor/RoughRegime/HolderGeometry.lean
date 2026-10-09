module

public import RoughRegime.HolderConstants
public import RoughRegime.UniformCube


@[expose] public section

/-! Geometry and derivative uniqueness on the source unit cube. -/
noncomputable section
open Set
open scoped BigOperators
namespace RoughRegime.Model

theorem convex_cube (d : ℕ) : Convex ℝ (cube d) := by
  intro x hx y hy a b ha hb hab j
  have hxj := hx j
  have hyj := hy j
  constructor
  · exact add_nonneg (mul_nonneg ha hxj.1) (mul_nonneg hb hyj.1)
  · change a * x j + b * y j ≤ 1
    calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hxj.2 ha)
        (mul_le_mul_of_nonneg_left hyj.2 hb)
      _ = 1 := by nlinarith

theorem isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  rw [cube_eq_preimage]
  exact (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem cube_nonempty_interior (d : ℕ) : (interior (cube d)).Nonempty := by
  let c : Covariate d := WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))
  refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 2))
  intro x hx j
  have hcoord : |x j - 1 / 2| < 1 / 2 := by
    have hb := PiLp.norm_apply_le (x - c) j
    have hd : ‖x - c‖ < 1 / 2 := by simpa [dist_eq_norm] using hx
    exact hb.trans_lt hd
  exact ⟨by linarith [(abs_lt.mp hcoord).1], by linarith [(abs_lt.mp hcoord).2]⟩

theorem uniqueDiffOn_cube (d : ℕ) : UniqueDiffOn ℝ (cube d) :=
  uniqueDiffOn_convex (convex_cube d) (cube_nonempty_interior d)

theorem coordinateDerivative_eq_iteratedFDeriv {d : ℕ} (f : Covariate d → ℝ)
    (q : ℕ) (σ : Fin q → Fin d) (x : Covariate d) (hx : x ∈ cube d)
    (hf : ContDiffAt ℝ q f x) :
    coordinateDerivative f q σ x =
      iteratedFDeriv ℝ q f x (fun j => EuclideanSpace.single (σ j) 1) := by
  unfold coordinateDerivative
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_cube d) hf hx]

end RoughRegime.Model
