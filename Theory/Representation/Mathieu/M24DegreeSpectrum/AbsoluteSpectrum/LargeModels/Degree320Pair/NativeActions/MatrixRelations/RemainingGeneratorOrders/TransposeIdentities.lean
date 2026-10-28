module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.GeneratorOrders
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposeAA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning.TransposeBB

/-!
# Literal transpose identities for the degree-320 generator pairs

The published 320b first generator is exactly the transpose of the 320a first
generator. The transpose of the 320b second generator is the stored candidate
for the square of the 320a second generator. The existing column certificates,
together with kernel-checked equalities of their output data, prove these facts.
Thus the already proved 320a square equation also supplies the 320b equation.
The second identity does not by itself certify the candidate square.

Source: the unchanged ATLAS degree-320 matrices, documented and hashed in
`Degree320Pair/source/README.md`, and John Bray's presentation M24G1-P1.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
open Thompson.BinaryMatrix MatrixCertificates.OrbitCertificates

set_option maxRecDepth 2000 in
/-- Equality of the literal first generators, without any change of basis. -/
theorem matrixA_true_eq_transpose_false : matrixA true = (matrixA false).transpose := by
  have hd : MatrixCertificates.OrbitCertificates.Data.AATranspose = Degree320Pair.Data.Ab := by
    apply congrArg List.toArray
    decide +kernel
  change decode 320 Degree320Pair.Data.Ab = (decode 320 Degree320Pair.Data.Aa).transpose
  rw [transpose_decode 320 _ _ TransposeAA.check, hd]

set_option maxRecDepth 2000 in
/-- The literal transpose is the square candidate; its product check is separate. -/
theorem transpose_matrixB_true_eq_square_candidate :
    (matrixB true).transpose = decode 320 squareBaRows.toArray := by
  have hd : MatrixCertificates.OrbitCertificates.Data.BBTranspose = squareBaRows.toArray := by
    apply congrArg List.toArray
    decide +kernel
  change (decode 320 Degree320Pair.Data.Bb).transpose = _
  rw [transpose_decode 320 _ _ TransposeBB.check, hd]

/-- The first source relation for 320b follows from the existing 320a proof. -/
theorem square_matrixA_true : matrixA true ^ 2 = 1 := by
  rw [matrixA_true_eq_transpose_false, ← Matrix.transpose_pow, square_matrixA_false,
    Matrix.transpose_one]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
