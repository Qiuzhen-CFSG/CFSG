module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.RemainingGeneratorOrders.TransposeIdentities
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.RemainingGeneratorOrders.SquareBA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.RemainingGeneratorOrders.CubeBA

/-!
# The remaining degree-320 ATLAS generator equations

The existing trace certificate proves the literal square of Ba, and one new
sparse row certificate proves Ba times that square is the identity. The
published 320b matrices satisfy Ab = Aaᵀ and Bb = (Ba²)ᵀ, as certified by the
existing transpose checks. Powers and transposition therefore supply the 320b
square and cube equations from the corresponding 320a equations.

The two `rowRelatorValues` applications discharge exactly the first two clauses
of John Bray's ATLAS presentation M24G1-P1. In particular, `square_matrixA_true`
and `cube_matrixB` supply hA and hB of `matrixRelations_of_remaining`. The five
longer source relators remain with that theorem's assembly owner. No group
action, presentation comparison, density, or trace premise is assumed.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/M24G1-P1.
The unchanged numerical matrices and hashes are documented in
`Degree320Pair/source/README.md`; proof reuse and measurements are in
`RemainingGeneratorOrders/source/README.md`.
-/

@[expose] public section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
open Thompson.BinaryMatrix
private theorem square_matrixB_false_candidate :
    matrixB false ^ 2 = decode 320 squareBaRows.toArray := by
  rw [pow_two]
  exact product_sound_list 320 Data.BaRows Data.BaRows squareBaRows
    (by decide +kernel) (by decide +kernel) SquareBA_checked

/-- The exact contragredient identity for the literal second generators. -/
theorem matrixB_true_eq_transpose_square_false :
    matrixB true = (matrixB false ^ 2).transpose := by
  rw [square_matrixB_false_candidate, ← transpose_matrixB_true_eq_square_candidate,
    Matrix.transpose_transpose]

/-- The second source relation for both literal, untransposed ATLAS pairs. -/
theorem cube_matrixB (variant : Bool) : matrixB variant ^ 3 = 1 := by
  have hc : matrixB false ^ 3 = 1 := by
    rw [show (3 : Nat) = 1 + 2 from rfl, pow_add, pow_one, square_matrixB_false_candidate]
    exact (product_sound_list 320 Data.BaRows squareBaRows identityRows
      (by decide +kernel) (by decide +kernel) CubeBA_checked).trans decode_identityRows
  cases variant with
  | false => exact hc
  | true =>
    rw [matrixB_true_eq_transpose_square_false, ← Matrix.transpose_pow,
      ← pow_mul, Nat.mul_comm 2 3, pow_mul, hc, one_pow, Matrix.transpose_one]

/-- Literal application to source clause zero, reusing the established 320a square. -/
theorem rowRelatorValues_zero (variant : Bool) :
    Degrees12421792.NativeActions.Presentation.rowRelatorValues
      (matrixA variant) (matrixB variant) 0 = 1 := by
  change matrixA variant ^ 2 = 1
  cases variant with
  | false => exact square_matrixA_false
  | true => exact square_matrixA_true

/-- Literal application to source clause one for either variant. -/
theorem rowRelatorValues_one (variant : Bool) :
    Degrees12421792.NativeActions.Presentation.rowRelatorValues
      (matrixA variant) (matrixB variant) 1 = 1 := by
  exact cube_matrixB variant
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
