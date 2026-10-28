module
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointOrbit
import Mathlib.Tactic.Ring

/-!
# The irreducible section of a nonsingular point hyperplane

An invariant additive subgroup between the fixed field line and its
perpendicular hyperplane is either endpoint. Subtracting a scalar square root
of the determinant from a nonscalar trace-zero matrix produces a nonzero
singular vector. The literal diagonal orbit of that vector generates the
whole hyperplane. This argument retains additive subgroups and therefore
applies after restricting scalars to the prime field.

Source application: Aschbacher--Smith 9.1.2(4) and9.4.1, printed pp.729,735.
-/

public section
open Matrix Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix.PointOrbit
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
private theorem traceZero_sub_scalar_det (M : Mat (F := F))
    (ht : M.trace = 0) (c : F) :
    (M - c • (1 : Mat (F := F))).det = M.det + c^2 := by
  have hd : M 0 0 = M 1 1 := by
    simpa [Matrix.trace,Fin.sum_univ_two,CharTwo.add_eq_zero] using ht
  have h2 : (2:F) = 0 := by exact CharP.cast_eq_zero F 2
  simp only [det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, if_true, mul_one]
  rw [←hd]
  ring_nf
  simp [h2]

omit [Finite F] in
/-- In characteristic two, a nonsingular point lies in its own perpendicular hyperplane. -/
theorem pointLine_le_pointHyperplane (v : Mat (F := F)) (hv : v.det ≠ 0) :
    Submodule.span F ({v} : Set (Mat (F := F))) ≤ pointHyperplane v := by
  apply Submodule.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  change (v*v⁻¹).trace = 0
  rw [Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)]
  simp only [Matrix.trace,Fin.sum_univ_two]
  exact CharTwo.add_self_eq_zero 1

/-- The fixed field line is the only proper invariant subgroup containing it
in the nonsingular point hyperplane, including for the additive group action. -/
theorem pointHyperplane_interval (v : Mat (F := F)) (hv : v.det ≠ 0)
    (W : AddSubgroup (Mat (F := F)))
    (hW : ∀ g : pointStabilizer v, ∀ M ∈ W, matrixAction g.val M ∈ W)
    (hline : (Submodule.span F ({v} : Set (Mat (F := F)))).toAddSubgroup ≤ W)
    (hplane : W ≤ (pointHyperplane v).toAddSubgroup) :
    W = (Submodule.span F ({v} : Set (Mat (F := F)))).toAddSubgroup ∨
      W = (pointHyperplane v).toAddSubgroup := by
  classical
  by_cases he : W ≤ (Submodule.span F ({v} : Set (Mat (F := F)))).toAddSubgroup
  · exact Or.inl (le_antisymm he hline)
  · right
    change ¬ ∀ z, z ∈ W → z ∈ (Submodule.span F ({v} : Set (Mat (F := F)))).toAddSubgroup at he
    push Not at he
    obtain ⟨z,hz,hzl⟩ := he
    let M := z * v⁻¹
    have ht : M.trace = 0 := hplane hz
    obtain ⟨c,hc⟩ := (Finite.surjective_of_injective (f := fun c : F => c^2)
      CharTwo.sq_injective) M.det
    change c^2 = M.det at hc
    have hi : v⁻¹*v = 1 := Matrix.nonsing_inv_mul v (isUnit_iff_ne_zero.mpr hv)
    have hi' : v*v⁻¹ = 1 := Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)
    have hcv : c • v ∈ W := hline (Submodule.smul_mem _ c (Submodule.subset_span (by simp)))
    have hd : (z-c•v).det = 0 := by
      have he : z-c•v = (M-c•(1 : Mat (F := F)))*v := by
        simp [M,sub_mul,mul_assoc,hi]
      rw [he,Matrix.det_mul,traceZero_sub_scalar_det M ht,hc,CharTwo.add_self_eq_zero,zero_mul]
    have hn : z-c•v ≠ 0 := by
      intro he
      apply hzl
      rw [sub_eq_zero.mp he]
      exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    have hp : z-c•v ∈ pointHyperplane v := by
      rw [mem_pointHyperplane,sub_mul,Matrix.smul_mul,hi',Matrix.trace_sub,Matrix.trace_smul]
      change M.trace - c*(1 : Mat (F := F)).trace = 0
      rw [ht]
      have htr : (1 : Mat (F := F)).trace = 0 := by
        simp only [Matrix.trace,Fin.sum_univ_two]
        exact CharTwo.add_self_eq_zero 1
      rw [htr]
      simp
    exact le_antisymm hplane (pointHyperplane_le_of_singular v hv W hW
      (z-c•v) (W.sub_mem hz hcv) hn hd hp)
end ClassicalOrthogonal.FourPlusMatrix.PointOrbit
