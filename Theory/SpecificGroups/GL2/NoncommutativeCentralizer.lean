module
public import Theory.LinearAlgebra.MatrixTwoCentralizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Scalar centralizers of noncommutative GL2 subgroups

Over any field, the centralizer of a noncommutative subgroup of GL2 consists
of scalar matrices. The theorem concerns the actual subgroup and the actual
scalar homomorphism from field units. It requires no finiteness,
characteristic, irreducibility, or semisimplicity assumptions.

A nonscalar two-by-two matrix has commutative matrix centralizer, by the
linear-combination characterization in MatrixTwoCentralizer. If such a
matrix centralized the given subgroup, the subgroup would therefore be
commutative. Thus every centralizing matrix is scalar; the existing GL
center characterization identifies it with a scalar from the field units.

This provides the matrix-centralizer step in ABG II.3 Proposition 3(iv),
article pages 27–28, before imposing the determinant-level condition that
makes the scalar centralizer a two-group.
-/

namespace Matrix.GeneralLinearGroup

public theorem centralizer_le_scalar_of_noncommutative
    {F : Type*} [Field F] (U : Subgroup (GL (Fin 2) F)) (hU : ¬ IsMulCommutative U) :
    Subgroup.centralizer (U : Set (GL (Fin 2) F)) ≤
      (scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range := by
  rw [← center_eq_range_scalar]
  intro x hx
  apply mem_center_iff_val_mem_range_scalar.mpr
  by_contra hscalar
  have hA : ¬ ∃ a : F, x.val = a • 1 := by
    rintro ⟨a, ha⟩
    apply hscalar
    refine ⟨a, ?_⟩
    rw [ha]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  apply hU
  apply IsMulCommutative.of_comm
  intro B C
  apply Subtype.ext
  apply Units.ext
  apply Matrix.commute_of_commute_nonscalar_two x.val B.val.val C.val.val hA
  · exact congrArg Units.val ((Subgroup.mem_centralizer_iff.mp hx) B.val B.property).symm
  · exact congrArg Units.val ((Subgroup.mem_centralizer_iff.mp hx) C.val C.property).symm

end Matrix.GeneralLinearGroup
