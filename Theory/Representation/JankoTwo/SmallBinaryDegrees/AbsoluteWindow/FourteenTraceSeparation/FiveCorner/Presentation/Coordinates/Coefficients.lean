module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Arithmetic

/-!
# Assembly of the reverse-norm coefficient certificate

The coefficient problem splits into two independent finite computations:
the two cached subgroup actions must evaluate the original long words, and
the packed columns computed with that cache must equal the columns of the
unchanged operator arrays. This module proves their exact assembly, without
asserting either remaining computation. The original coefficient definition,
word multiplicities, and input-row/output-column convention are preserved.

The result supplies the arithmetic premise of
`Presentation.literalCoordinates_of_certificates`; its geometric premise is
independent. Source: Coordinates/source/README.md and the reverse-norm formula.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData

/-- Assemble the two finite checks into the literal coefficient contract. -/
theorem coefficientCertificate_of_checks
    (hS : Coefficients.SubgroupActionsCorrect) (hC : Coefficients.ColumnChecks) :
    CoefficientCertificate := by
  intro k i j
  calc
    countEntry k i j =
        Coefficients.bit (Coefficients.column Coefficients.leftAction Coefficients.rightAction k j)
          i.val := (Coefficients.bit_column _ _ hS.1 hS.2 k i j).symm
    _ = Coefficients.bit (Coefficients.columnFromRows j.val (rows k).toList) i.val :=
      congrArg (fun n => Coefficients.bit n i.val) (hC k j)
    _ = entry k i j := Coefficients.bit_columnFromRows k i j

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData
