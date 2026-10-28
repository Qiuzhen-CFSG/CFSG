module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Operators
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.Tables
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.Generation
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsB
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsC
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Decoding

/-!
# Certificate assembly for the fixed Hall--Janko coordinate operators

The arithmetic checker translates packed XORs into the exact coordinate
operators, words and relations. The checked word vectors and inverse rows
prove that words span all 1008 coordinates. The three polynomial batches
cover the entire numeral relation list; exact decoding identifies that list
with the unchanged string-encoded certificate, including all monomials.

Thus both finite premises of `Presentation.presentation_of_coordinates` are
discharged. The independent literal-coordinate realization remains with its
producer; this module needs no group-model assumptions.

Source: `Presentation/source/README.md` and the unchanged shared certificate.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates

/-- Decoding and packed vanishing are independent obligations. Their assembly
proves the original coordinate relation contract, including every source term. -/
theorem coordinateRelations_of_reencoded (rs : List Certificate.Relation)
    (hdecode : Certificate.relations = rs)
    (hzero : ∀ r ∈ rs, relation r = 0) : CoordinateRelations := by
  apply coordinateRelations_of_checks
  simpa only [hdecode] using hzero

/-- Words in the nine unchanged operators span every binary coordinate vector. -/
theorem coordinateWordSpan : CoordinateWordSpan :=
  Generation.coordinateWordSpan

/-- All 87 unchanged source relations vanish for the original operators and seed. -/
theorem coordinateRelations : CoordinateRelations := by
  apply coordinateRelations_of_reencoded MatrixCertificate.numericalRelations
    MatrixCertificate.relations_eq_numericalRelations
  have cover (rs : List Certificate.Relation) :
      rs.take 28 ++ (rs.drop 28).take 32 ++ rs.drop 60 = rs := by
    rw [List.append_assoc, ← List.drop_drop (i := 32) (j := 28),
      List.take_append_drop, List.take_append_drop]
  intro r hr
  rw [← cover MatrixCertificate.numericalRelations,
    List.mem_append, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · exact PolynomialsA.checks r hr
  · exact PolynomialsB.checks r hr
  · exact PolynomialsC.checks r hr

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates
