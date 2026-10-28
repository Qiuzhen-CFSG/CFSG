module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair14.Actions

/-!
# Polynomial checks for generators 1 and 4

The verified table checks every monomial of the unchanged numerical rows.
Codes 0 and 1 both evaluate to the packed seed, so constant terms are retained.

The data come from the unchanged arrays and polynomial rows documented in
`Presentation/source/README.md`. Every numerical equality is checked in Lean's
kernel; the generating Python program is not part of the trusted proof.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair14

lemma steps_check : ∀ n ∈ codes, 2 ≤ n →
    action (if n.testBit 0 then 4 else 1) (table (n / 2)) = table n := by
  apply steps_support
  rw [list_partition]
  simp only [List.append_assoc]
  exact (steps_append check00 (steps_append check01 (steps_append check02 (steps_append check03 (steps_append check04 (steps_append check05 (steps_append check06 (steps_append check07 (steps_append check08 (steps_append check09 (steps_append check10 (steps_append check11 (steps_append check12 (steps_append check13 (steps_append check14 (steps_append check15 (steps_append check16 (steps_append check17 (steps_append check18 (steps_append check19 (steps_append check20 (steps_append check21 (steps_append check22 (steps_append check23 (steps_append check24 (steps_append check25 (steps_append check26 (steps_append check27 (steps_append check28 (steps_append check29 (steps_append check30 check31)))))))))))))))))))))))))))))))

lemma row20 : relation MatrixCertificate.NumericalData.row20 = 0 :=
  (relation_eq_table MatrixCertificate.NumericalData.row20 table codes seed_check parent_check steps_check covered20).trans zero20

lemma row21 : relation MatrixCertificate.NumericalData.row21 = 0 :=
  (relation_eq_table MatrixCertificate.NumericalData.row21 table codes seed_check parent_check steps_check covered21).trans zero21

lemma row22 : relation MatrixCertificate.NumericalData.row22 = 0 :=
  (relation_eq_table MatrixCertificate.NumericalData.row22 table codes seed_check parent_check steps_check covered22).trans zero22


end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair14
