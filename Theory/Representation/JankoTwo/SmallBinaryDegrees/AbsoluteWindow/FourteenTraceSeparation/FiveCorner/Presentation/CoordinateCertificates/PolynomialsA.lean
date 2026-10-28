module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.Tables
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair01
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair02
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair03
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair04
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair05
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair06
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair07
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair12
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair13
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair14
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair15
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair16

/-!
# First twelve pairs of the fixed Hall--Janko coordinate certificate

The 28 source rows use twelve shared prefix tables, with kernel-checked
right-action steps and XOR sums. Decoding gives the same polynomial vanishing
for the actual additive coordinate operators and their original seed.

The data come from the unchanged arrays and polynomial rows documented in
`Presentation/source/README.md`. Every numerical equality is checked in Lean's
kernel; the generating Python program is not part of the trusted proof.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA

/-- Exactly rows 00–27 of the unchanged numerical list. -/
lemma checks : ∀ r ∈ MatrixCertificate.numericalRelations.take 28,
    CoordinateCertificates.relation r = 0 := by
  intro r hr
  change r ∈ [MatrixCertificate.NumericalData.row00, MatrixCertificate.NumericalData.row01, MatrixCertificate.NumericalData.row02, MatrixCertificate.NumericalData.row03, MatrixCertificate.NumericalData.row04, MatrixCertificate.NumericalData.row05, MatrixCertificate.NumericalData.row06, MatrixCertificate.NumericalData.row07, MatrixCertificate.NumericalData.row08, MatrixCertificate.NumericalData.row09, MatrixCertificate.NumericalData.row10, MatrixCertificate.NumericalData.row11, MatrixCertificate.NumericalData.row12, MatrixCertificate.NumericalData.row13, MatrixCertificate.NumericalData.row14, MatrixCertificate.NumericalData.row15, MatrixCertificate.NumericalData.row16, MatrixCertificate.NumericalData.row17, MatrixCertificate.NumericalData.row18, MatrixCertificate.NumericalData.row19, MatrixCertificate.NumericalData.row20, MatrixCertificate.NumericalData.row21, MatrixCertificate.NumericalData.row22, MatrixCertificate.NumericalData.row23, MatrixCertificate.NumericalData.row24, MatrixCertificate.NumericalData.row25, MatrixCertificate.NumericalData.row26, MatrixCertificate.NumericalData.row27] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Pair01.row00
  · exact Pair01.row01
  · exact Pair02.row02
  · exact Pair02.row03
  · exact Pair02.row04
  · exact Pair03.row05
  · exact Pair03.row06
  · exact Pair04.row07
  · exact Pair04.row08
  · exact Pair04.row09
  · exact Pair05.row10
  · exact Pair05.row11
  · exact Pair05.row12
  · exact Pair06.row13
  · exact Pair07.row14
  · exact Pair12.row15
  · exact Pair12.row16
  · exact Pair12.row17
  · exact Pair13.row18
  · exact Pair13.row19
  · exact Pair14.row20
  · exact Pair14.row21
  · exact Pair14.row22
  · exact Pair15.row23
  · exact Pair15.row24
  · exact Pair16.row25
  · exact Pair16.row26
  · exact Pair16.row27

/-- The same 28 polynomials vanish for the original coordinate operators. -/
lemma operator_checks : ∀ r ∈ MatrixCertificate.numericalRelations.take 28,
    runRelation (fun k => operator k) seed r = 0 := by
  intro r hr
  rw [← decode_relation, checks r hr, decode_zero]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA
