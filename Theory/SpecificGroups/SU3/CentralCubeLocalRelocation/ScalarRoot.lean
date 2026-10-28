module
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.Algebra.Polynomial.SpecificDegree
/-!
# A cube root forced by a special-linear scalar cube

Suppose a three-dimensional matrix has scalar cube z. If z has no cube root in
the ground field, the cubic X³−z is irreducible. It is then the minimal polynomial
of the matrix and, by degree, its characteristic polynomial. Comparing constant
terms gives determinant z. Consequently determinant one forces a cube root in
the ground field, including the immediate case z=1.

This field-level argument supplies the scalar-root step in the central-cube
localization of SU₃; it requires neither a finite field nor a Hermitian form.
The consumer is the central-cube branch for the special-unitary source model
in Aschbacher–Smith, combined manuscript of 1 March 2004.
-/

public section
open Polynomial Matrix
namespace Matrix
variable {F : Type*} [Field F]
/-- A scalar cube in dimension three either has scalar equal to the determinant
or has a cube root in the ground field. -/
theorem det_eq_or_exists_cube_root_of_cube_scalar (M : Matrix (Fin 3) (Fin 3) F)
    (z : F) (hM : M ^ 3 = Matrix.scalar (Fin 3) z) :
    M.det = z ∨ ∃ a : F, a ^ 3 = z := by
  by_cases hroot : ∃ a : F, a ^ 3 = z
  · exact Or.inr hroot
  left
  let p : F[X] := X ^ 3 - C z
  have hp : p.Monic := monic_X_pow_sub_C z (by decide : 3 ≠ 0)
  have hpdeg : p.natDegree = 3 := natDegree_X_pow_sub_C
  have hirr : Irreducible p := irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hpdeg]; decide) (by
      intro a ha
      apply hroot
      exact ⟨a, sub_eq_zero.mp (by simpa only [p,IsRoot,eval_sub,eval_pow,eval_X,eval_C] using ha)⟩)
  have heval : aeval M p = 0 := by
    simp only [p,map_sub,map_pow,aeval_X,aeval_C]
    rw [hM]
    simp only [Matrix.algebraMap_eq_diagonal,Matrix.scalar_apply,Pi.algebraMap_def,
      Algebra.algebraMap_self_apply,sub_self]
  have hmin : p = minpoly F M := minpoly.eq_of_irreducible_of_monic hirr heval hp
  have hchar : M.charpoly = p := eq_of_monic_of_dvd_of_natDegree_le hp M.charpoly_monic
    (hmin ▸ M.minpoly_dvd_charpoly) (by simp [hpdeg])
  have hd := Matrix.det_eq_sign_charpoly_coeff M
  simpa [hchar,p,coeff_sub,coeff_X_pow,coeff_C,pow_succ] using hd

/-- Every scalar cube of a determinant-one three-dimensional matrix has a cube
root in the ground field. -/
theorem exists_cube_root_of_det_one_cube_scalar (M : Matrix (Fin 3) (Fin 3) F)
    (hdet : M.det = 1) (z : F) (hM : M ^ 3 = Matrix.scalar (Fin 3) z) :
    ∃ a : F, a ^ 3 = z := by
  rcases M.det_eq_or_exists_cube_root_of_cube_scalar z hM with hz | hroot
  · exact ⟨1, by simpa only [one_pow,hdet] using hz⟩
  · exact hroot
end Matrix
