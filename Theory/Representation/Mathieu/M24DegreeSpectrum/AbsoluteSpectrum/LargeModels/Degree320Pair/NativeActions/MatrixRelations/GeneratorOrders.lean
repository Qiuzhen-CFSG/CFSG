module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.SquareAA

/-!
# The first generator equation for the literal degree-320a pair

Forty bounded kernel checks prove A² = 1 on the original, untransposed
320a matrix. This discharges the first clause of Bray's M24G1-P1 for this
variant. The corresponding 320b equation and both cube equations remain
independent finite certificates. No group action or presentation comparison
is assumed.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
open Thompson.BinaryMatrix

/-- The first source equation for the literal 320a matrix. The other
variant and the cube equations are independent remaining certificates. -/
theorem square_matrixA_false : matrixA false ^ 2 = 1 := by
  rw [pow_two]
  change decode 320 Data.AaRows.toArray * decode 320 Data.AaRows.toArray = 1
  exact (product_sound_list 320 Data.AaRows Data.AaRows identityRows
    (by decide +kernel) (by decide +kernel) SquareAA_checked).trans decode_identityRows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
