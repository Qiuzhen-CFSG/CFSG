module

public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# The diagonal predicate in the actual unitary monomial group

This predicate means that the underlying matrix is diagonal, independently
of any proposed permutation action. Diagonal matrices commute, so a
permutation action whose kernel consists of these matrices has abelian kernel.
It is the shared matrix interface between the coordinate-line action and the
normal diagonal sign subgroup calculations.

Source: GLS3, Theorem 6.5.3(b), `refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section

namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial

variable {E : Type*} [Field E] {J : HermitianForm 3 E}

/-- Diagonality of the underlying special-unitary matrix. -/
def IsDiagonal (x : special J) : Prop := Matrix.IsDiag x.val.val.val

/-- Two diagonal members of the actual monomial subgroup commute. -/
theorem commute_of_isDiagonal {x y : special J}
    (hx : IsDiagonal x) (hy : IsDiagonal y) : Commute x y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change x.val.val.val * y.val.val.val = y.val.val.val * x.val.val.val
  rw [← hx.diagonal_diag, ← hy.diagonal_diag]
  exact (Matrix.commute_diagonal _ _).eq

/-- A matrix action with diagonal kernel has abelian kernel. -/
theorem isMulCommutative_kernel_of_isDiagonal
    (f : special J →* Equiv.Perm (Fin 3))
    (hker : ∀ x : special J, f x = 1 → IsDiagonal x) :
    IsMulCommutative f.ker := by
  exact .of_setLike_mul_comm fun x hx y hy =>
    (commute_of_isDiagonal (hker x hx) (hker y hy)).eq

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial
