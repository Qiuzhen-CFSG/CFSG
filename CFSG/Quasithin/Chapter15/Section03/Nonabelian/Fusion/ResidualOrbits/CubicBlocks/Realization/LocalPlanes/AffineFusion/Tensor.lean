module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Orthogonality
/-!
# Cubic orbits and the two determinant hyperplanes

The three translates of every tensor include one orthogonal to a given
vector. For a nonzero singular vector, the only orbits missing the other
polar value lie in its cubic line. The first calculation reduces to eight
binary coordinates; the second checks the sixteen tensors and their three
translates in the kernel.

Source: Aschbacher–Smith, proof of 15.3.61(2), printed p.1150.
-/

@[expose] public section
open Subgroup Matrix
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.AffineFusion

private theorem cubic_polar_zero (j : Fin 2) (z v : TensorVector) :
    determinantPolar z v = 0 ∨
    determinantPolar z (tensorAction (complementaryRotation j) v) = 0 ∨
    determinantPolar z (tensorAction (complementaryRotation j)
      (tensorAction (complementaryRotation j) v)) = 0 := by
  fin_cases j <;>
    simp [determinantPolar, complementaryRotation, tensorAction_apply, rotation,
      Matrix.det_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  all_goals
    generalize z.toAdd 0 0 = a, z.toAdd 0 1 = b, z.toAdd 1 0 = c, z.toAdd 1 1 = d
    generalize v.toAdd 0 0 = e, v.toAdd 0 1 = f, v.toAdd 1 0 = g, v.toAdd 1 1 = h
    revert a b c d e f g h
    decide +kernel

set_option synthInstance.maxSize 256 in
private theorem cubic_polar_one : ∀ (j : Fin 2) (z v : TensorVector),
    z ≠ 1 → z.toAdd.det = 0 → v ≠ 1 → v ≠ z →
    v ≠ tensorAction (complementaryRotation j) z →
    v ≠ z * tensorAction (complementaryRotation j) z →
    ∃ n : Fin 3, determinantPolar z (tensorAction (complementaryRotation j ^ n.val) v) = 1 := by
  decide +kernel

/-- Every cubic tensor orbit meets the determinant hyperplane. -/
theorem exists_cubic_orthogonal (j : Fin 2) (z v : TensorVector) :
    ∃ n : Fin 3, determinantPolar z (tensorAction (complementaryRotation j ^ n.val) v) = 0 := by
  rcases cubic_polar_zero j z v with h | h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩
  · exact ⟨2, by simpa only [Fin.val_two, pow_two, map_mul, MulAut.mul_apply] using h⟩

/-- Off the singular cubic line, an orbit also meets the other affine hyperplane. -/
theorem exists_cubic_nonorthogonal (j : Fin 2) (z v : TensorVector)
    (hz : z ≠ 1) (hs : z.toAdd.det = 0) (hv : v ∉ tensorCubicLine j z) :
    ∃ n : Fin 3, determinantPolar z (tensorAction (complementaryRotation j ^ n.val) v) = 1 := by
  have hzL : z ∈ tensorCubicLine j z := mem_sup_left (mem_zpowers z)
  have hrL : tensorAction (complementaryRotation j) z ∈ tensorCubicLine j z :=
    mem_sup_right (mem_zpowers _)
  exact cubic_polar_one j z v hz hs
    (fun he => hv (he.symm ▸ (one_mem _)))
    (fun he => hv (he.symm ▸ hzL))
    (fun he => hv (he.symm ▸ hrL))
    (fun he => hv (he.symm ▸ (mul_mem hzL hrL)))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.AffineFusion
