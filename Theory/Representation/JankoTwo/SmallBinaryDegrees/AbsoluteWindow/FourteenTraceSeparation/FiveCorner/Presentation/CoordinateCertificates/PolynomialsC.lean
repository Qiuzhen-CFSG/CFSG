module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.Tables
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair47
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair56
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair57
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair67
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair08
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair18
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair28
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair38
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair48
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair58
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair68
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC.Pair78

/-!
# The last twelve coordinate polynomial pairs for J₂

All 27 rows of `numericalRelations.drop 60` vanish on the unchanged nine packed
operators. Each pair shares a table of word values: the binary parent is evaluated
first and the low bit applies the last generator on the right. Both empty-word
codes are the actual seed one. The descendants kernel-check every action and the
XOR of every monomial in each row. `operator_checks` transports the result to the
original additive operators and seed via `decode_relation`.

Source: `Presentation/source/README.md`, the retained
`complete-pair-certificates.json`, and `MatrixCertificate.NumericalData`.
Identification with the string-encoded source list belongs to the independent
decoding producer; this theorem uses precisely the stated numeral list.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC

theorem checks : ∀ r ∈ MatrixCertificate.numericalRelations.drop 60,
    CoordinateCertificates.relation r = 0 := by
  intro r hr
  change r ∈ [MatrixCertificate.NumericalData.row60, MatrixCertificate.NumericalData.row61, MatrixCertificate.NumericalData.row62, MatrixCertificate.NumericalData.row63, MatrixCertificate.NumericalData.row64, MatrixCertificate.NumericalData.row65, MatrixCertificate.NumericalData.row66, MatrixCertificate.NumericalData.row67, MatrixCertificate.NumericalData.row68, MatrixCertificate.NumericalData.row69, MatrixCertificate.NumericalData.row70, MatrixCertificate.NumericalData.row71, MatrixCertificate.NumericalData.row72, MatrixCertificate.NumericalData.row73, MatrixCertificate.NumericalData.row74, MatrixCertificate.NumericalData.row75, MatrixCertificate.NumericalData.row76, MatrixCertificate.NumericalData.row77, MatrixCertificate.NumericalData.row78, MatrixCertificate.NumericalData.row79, MatrixCertificate.NumericalData.row80, MatrixCertificate.NumericalData.row81, MatrixCertificate.NumericalData.row82, MatrixCertificate.NumericalData.row83, MatrixCertificate.NumericalData.row84, MatrixCertificate.NumericalData.row85, MatrixCertificate.NumericalData.row86] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Pair47.row60_check
  · exact Pair47.row61_check
  · exact Pair47.row62_check
  · exact Pair56.row63_check
  · exact Pair56.row64_check
  · exact Pair57.row65_check
  · exact Pair57.row66_check
  · exact Pair57.row67_check
  · exact Pair67.row68_check
  · exact Pair67.row69_check
  · exact Pair08.row70_check
  · exact Pair08.row71_check
  · exact Pair18.row72_check
  · exact Pair18.row73_check
  · exact Pair28.row74_check
  · exact Pair38.row75_check
  · exact Pair38.row76_check
  · exact Pair48.row77_check
  · exact Pair48.row78_check
  · exact Pair58.row79_check
  · exact Pair58.row80_check
  · exact Pair58.row81_check
  · exact Pair68.row82_check
  · exact Pair68.row83_check
  · exact Pair68.row84_check
  · exact Pair78.row85_check
  · exact Pair78.row86_check

/-- The same exact list vanishes for the original coordinate operators and seed. -/
theorem operator_checks : ∀ r ∈ MatrixCertificate.numericalRelations.drop 60,
    runRelation (fun k => operator k) seed r = 0 := by
  intro r hr
  rw [← decode_relation, checks r hr, decode_zero]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC
