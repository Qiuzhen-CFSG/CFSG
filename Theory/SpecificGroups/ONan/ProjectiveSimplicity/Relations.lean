module

public import Theory.SpecificGroups.ONan.MatrixModel
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.MatrixCertificates

/-!
# Certified relations of the O'Nan projective generators

The ATLAS standard generators satisfy a² = b⁴ = (ab)¹¹ = 1 projectively.
For the supplied linear lifts, (AB)¹¹ = 2I. Explicit intermediate matrices
allow each multiplication to be checked independently by kernel reduction.
These are relations of the concrete matrices, not presentation assumptions.

Source: https://brauer.maths.qmul.ac.uk/Atlas/spor/ON/#sgens and the matrix
sources preserved in `refs/original/onan/README.md`.
-/

namespace ONan

/-- The first projective generator is an involution. -/
public theorem generatorA_pow_two : generatorA ^ 2 = 1 := by
  have h : linearA ^ 2 = 1 := by
    apply Units.ext
    exact (pow_two matrixA).trans matrixA_mul_self
  apply Subtype.ext
  change projectiveA ^ 2 = 1
  simpa only [projectiveA, map_pow, map_one] using
    congrArg Matrix.ProjGenLinGroup.mk h

/-- The second projective generator has fourth power one. -/
public theorem generatorB_pow_four : generatorB ^ 4 = 1 := by
  have h : linearB ^ 4 = 1 := Units.ext Simplicity.matrixB_pow_four
  apply Subtype.ext
  change projectiveB ^ 4 = 1
  simpa only [projectiveB, map_pow, map_one] using
    congrArg Matrix.ProjGenLinGroup.mk h

/-- The product of the projective generators has eleventh power one. -/
public theorem generatorAB_pow_eleven : (generatorA * generatorB) ^ 11 = 1 := by
  let u : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩
  have h : (linearA * linearB) ^ 11 = Matrix.GeneralLinearGroup.scalar (Fin 45) u :=
    Units.ext Simplicity.matrixAB_pow_eleven
  apply Subtype.ext
  change (projectiveA * projectiveB) ^ 11 = 1
  simpa only [projectiveA, projectiveB, map_pow, map_mul,
    Matrix.ProjGenLinGroup.mk_scalar] using congrArg Matrix.ProjGenLinGroup.mk h

end ONan
