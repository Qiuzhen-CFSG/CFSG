module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Certificate
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows0
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows1
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows2
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows3
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows4
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows5
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows6
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding.Rows7

/-!
# Exact decoding of the shared J₂ five-corner relations

The 87 rows of `Certificate.relations` are exactly the numeral-form relations:
the two generator indices, the order of rows and words, and all 37,649
monomial occurrences are preserved. The row proofs use a proved ASCII
specification of the standard splitter and decimal parser, with explicit
character witnesses checked by the kernel.

This discharges precisely the input of
`MatrixCertificate.matrixCommutativity_of_decoding`. Its unconditional matrix
assembly belongs to `MatrixCertificate`, which can import this lower module.
Source data and word conventions are those documented in `Certificate.lean`.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate

/-- The shared decimal-string relations and their numeral presentation agree exactly. -/
theorem relations_eq_numericalRelations : Certificate.relations = numericalRelations := by
  exact (congrArg₂ List.cons Decoding.row00
    (congrArg₂ List.cons Decoding.row01
    (congrArg₂ List.cons Decoding.row02
    (congrArg₂ List.cons Decoding.row03
    (congrArg₂ List.cons Decoding.row04
    (congrArg₂ List.cons Decoding.row05
    (congrArg₂ List.cons Decoding.row06
    (congrArg₂ List.cons Decoding.row07
    (congrArg₂ List.cons Decoding.row08
    (congrArg₂ List.cons Decoding.row09
    (congrArg₂ List.cons Decoding.row10
    (congrArg₂ List.cons Decoding.row11
    (congrArg₂ List.cons Decoding.row12
    (congrArg₂ List.cons Decoding.row13
    (congrArg₂ List.cons Decoding.row14
    (congrArg₂ List.cons Decoding.row15
    (congrArg₂ List.cons Decoding.row16
    (congrArg₂ List.cons Decoding.row17
    (congrArg₂ List.cons Decoding.row18
    (congrArg₂ List.cons Decoding.row19
    (congrArg₂ List.cons Decoding.row20
    (congrArg₂ List.cons Decoding.row21
    (congrArg₂ List.cons Decoding.row22
    (congrArg₂ List.cons Decoding.row23
    (congrArg₂ List.cons Decoding.row24
    (congrArg₂ List.cons Decoding.row25
    (congrArg₂ List.cons Decoding.row26
    (congrArg₂ List.cons Decoding.row27
    (congrArg₂ List.cons Decoding.row28
    (congrArg₂ List.cons Decoding.row29
    (congrArg₂ List.cons Decoding.row30
    (congrArg₂ List.cons Decoding.row31
    (congrArg₂ List.cons Decoding.row32
    (congrArg₂ List.cons Decoding.row33
    (congrArg₂ List.cons Decoding.row34
    (congrArg₂ List.cons Decoding.row35
    (congrArg₂ List.cons Decoding.row36
    (congrArg₂ List.cons Decoding.row37
    (congrArg₂ List.cons Decoding.row38
    (congrArg₂ List.cons Decoding.row39
    (congrArg₂ List.cons Decoding.row40
    (congrArg₂ List.cons Decoding.row41
    (congrArg₂ List.cons Decoding.row42
    (congrArg₂ List.cons Decoding.row43
    (congrArg₂ List.cons Decoding.row44
    (congrArg₂ List.cons Decoding.row45
    (congrArg₂ List.cons Decoding.row46
    (congrArg₂ List.cons Decoding.row47
    (congrArg₂ List.cons Decoding.row48
    (congrArg₂ List.cons Decoding.row49
    (congrArg₂ List.cons Decoding.row50
    (congrArg₂ List.cons Decoding.row51
    (congrArg₂ List.cons Decoding.row52
    (congrArg₂ List.cons Decoding.row53
    (congrArg₂ List.cons Decoding.row54
    (congrArg₂ List.cons Decoding.row55
    (congrArg₂ List.cons Decoding.row56
    (congrArg₂ List.cons Decoding.row57
    (congrArg₂ List.cons Decoding.row58
    (congrArg₂ List.cons Decoding.row59
    (congrArg₂ List.cons Decoding.row60
    (congrArg₂ List.cons Decoding.row61
    (congrArg₂ List.cons Decoding.row62
    (congrArg₂ List.cons Decoding.row63
    (congrArg₂ List.cons Decoding.row64
    (congrArg₂ List.cons Decoding.row65
    (congrArg₂ List.cons Decoding.row66
    (congrArg₂ List.cons Decoding.row67
    (congrArg₂ List.cons Decoding.row68
    (congrArg₂ List.cons Decoding.row69
    (congrArg₂ List.cons Decoding.row70
    (congrArg₂ List.cons Decoding.row71
    (congrArg₂ List.cons Decoding.row72
    (congrArg₂ List.cons Decoding.row73
    (congrArg₂ List.cons Decoding.row74
    (congrArg₂ List.cons Decoding.row75
    (congrArg₂ List.cons Decoding.row76
    (congrArg₂ List.cons Decoding.row77
    (congrArg₂ List.cons Decoding.row78
    (congrArg₂ List.cons Decoding.row79
    (congrArg₂ List.cons Decoding.row80
    (congrArg₂ List.cons Decoding.row81
    (congrArg₂ List.cons Decoding.row82
    (congrArg₂ List.cons Decoding.row83
    (congrArg₂ List.cons Decoding.row84
    (congrArg₂ List.cons Decoding.row85
    (congrArg₂ List.cons Decoding.row86
    rfl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
