module

public import Theory.Representation.GLTwoBorel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Two concrete Bruhat cells in GL₂

An invertible two-by-two matrix either lies in the upper triangular Borel,
or its lower-left entry is nonzero. In the latter case Gaussian elimination
expresses it as an upper triangular matrix times the coordinate swap times
an upper unipotent. Thus the Borel has exactly two double cosets. This is
the elementary rank-one Bruhat decomposition needed for principal-series
endomorphisms, including characteristic two and the field with two elements.
The argument is a direct matrix calculation rather than an appeal to an
abstract BN-pair or a character table.
-/

open scoped MatrixGroups

namespace GLTwo

variable {F : Type*} [Field F]

@[expose] public def borelWeyl (F : Type*) [Field F] : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

@[simp] public theorem borelWeyl_not_mem : borelWeyl F ∉ borelSubgroup F := by
  simp [borelWeyl]

@[simp] public theorem borelWeyl_mul_self : borelWeyl F * borelWeyl F = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [borelWeyl, Matrix.mul_apply, Fin.sum_univ_two]

public theorem borel_bruhat (matrix : GL (Fin 2) F) :
    matrix ∈ borelSubgroup F ∨
      ∃ left right : borelSubgroup F,
        matrix = left.val * borelWeyl F * right.val := by
  by_cases hlower : matrix 1 0 = 0
  · exact Or.inl hlower
  have hfirst : matrix 0 1 - matrix 0 0 * matrix 1 1 / matrix 1 0 ≠ 0 := by
    intro hzero
    apply matrix.det_ne_zero
    rw [Matrix.det_fin_two]
    have heq := (sub_eq_zero.mp hzero)
    have hmul : matrix 0 1 * matrix 1 0 = matrix 0 0 * matrix 1 1 :=
      (eq_div_iff hlower).mp heq
    exact sub_eq_zero.mpr hmul.symm
  let left : borelSubgroup F :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![matrix 0 1 - matrix 0 0 * matrix 1 1 / matrix 1 0, matrix 0 0;
        0, matrix 1 0] (by simpa [Matrix.det_fin_two] using mul_ne_zero hfirst hlower),
      by simp⟩
  refine Or.inr ⟨left, upperUnipotent F (matrix 1 1 / matrix 1 0), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [left, borelWeyl, upperUnipotent, Matrix.GeneralLinearGroup.upperRightHom,
      Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
    ring
  · field_simp

end GLTwo
