module

public import Theory.SpecificGroups.ONan.MatrixModel
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.RelationData

/-!
# Certified relations of the O'Nan projective generators

The ATLAS standard generators satisfy a² = b⁴ = (ab)¹¹ = 1 projectively.
For the supplied linear lifts, (AB)¹¹ = 2I. Explicit intermediate matrices
allow each multiplication to be checked independently by kernel reduction.
These are relations of the concrete matrices, not presentation assumptions.

Source: https://brauer.maths.qmul.ac.uk/Atlas/spor/ON/#sgens and the matrix
sources preserved in `refs/original/onan/README.md`.
-/

namespace ONan.Simplicity

open ONan.SimplicityData

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem b_sq : matrixB * matrixB = b2 := by
  apply Matrix.ext
  unfold b2
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem b2_sq : b2 * b2 = 1 := by
  apply Matrix.ext
  simp only [Matrix.one_apply]
  unfold b2
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem ab_eq : matrixA * matrixB = ab := by
  apply Matrix.ext
  unfold ab
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem ab_sq : ab * ab = ab2 := by
  apply Matrix.ext
  unfold ab ab2
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem ab2_sq : ab2 * ab2 = ab4 := by
  apply Matrix.ext
  unfold ab2 ab4
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem ab4_sq : ab4 * ab4 = ab8 := by
  apply Matrix.ext
  unfold ab4 ab8
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem ab8_mul_ab2 : ab8 * ab2 = ab10 := by
  apply Matrix.ext
  unfold ab8 ab2 ab10
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem ab10_mul_ab : ab10 * ab = Matrix.scalar (Fin 45) (2 : ZMod 7) := by
  apply Matrix.ext
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold ab10 ab
  decide +kernel

/-- The linear second generator has fourth power one. -/
public theorem matrixB_pow_four : matrixB ^ 4 = 1 := by
  calc
    matrixB ^ 4 = matrixB ^ 2 * matrixB ^ 2 := pow_add matrixB 2 2
    _ = 1 := by simp only [pow_two, b_sq, b2_sq]

/-- The eleventh power of the linear product is the scalar matrix 2I. -/
public theorem matrixAB_pow_eleven :
    (matrixA * matrixB) ^ 11 = Matrix.scalar (Fin 45) (2 : ZMod 7) := by
  have h2 : ab ^ 2 = ab2 := (pow_two ab).trans ab_sq
  have h4 : ab ^ 4 = ab4 := by
    calc
      ab ^ 4 = ab ^ 2 * ab ^ 2 := pow_add ab 2 2
      _ = ab4 := by rw [h2, ab2_sq]
  have h8 : ab ^ 8 = ab8 := by
    calc
      ab ^ 8 = ab ^ 4 * ab ^ 4 := pow_add ab 4 4
      _ = ab8 := by rw [h4, ab4_sq]
  rw [ab_eq]
  calc
    ab ^ 11 = (ab ^ 8 * ab ^ 2) * ab := by rw [← pow_add, ← pow_succ]
    _ = _ := by rw [h8, h2, ab8_mul_ab2, ab10_mul_ab]

end ONan.Simplicity
