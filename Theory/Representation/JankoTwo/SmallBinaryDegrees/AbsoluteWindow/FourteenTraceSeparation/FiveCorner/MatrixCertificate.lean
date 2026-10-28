module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Certificate
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalConsequence
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding

/-!
# Finite-matrix assembly for the J₂ five-corner certificate

The numeral-form relations force all nine binary matrices to commute. Exact
decoding identifies the shared string data with those numeral-form relations,
so `matrixCommutativity` proves the literal `Certificate.MatrixCommutativity`
contract with no extra premise. It supplies the matrix input to
`FiveCorner.exclusion_of_certificate`; the literal group-algebra presentation
is an independent obligation of that consumer.

Source conventions are those of `FiveCorner/Certificate.lean`; the numerical
consequence is kernel-checked in the descendants of this module.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
open Certificate

/-- Assembly after verifying the decimal decoding of the shared data. -/
theorem matrixCommutativity_of_decoding (hdec : relations = numericalRelations) :
    MatrixCommutativity := by
  intro x hx i j
  apply numerical_commutativity x _ i j
  simpa only [Satisfies, ← hdec] using hx

/-- The exact shared polynomial relations force every pair of binary matrices to commute. -/
theorem matrixCommutativity : MatrixCommutativity :=
  matrixCommutativity_of_decoding relations_eq_numericalRelations

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
