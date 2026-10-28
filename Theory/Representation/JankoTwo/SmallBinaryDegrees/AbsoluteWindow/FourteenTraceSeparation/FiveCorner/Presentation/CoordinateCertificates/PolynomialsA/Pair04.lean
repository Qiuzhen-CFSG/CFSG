module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair04.Actions

/-!
# Polynomial checks for generators 0 and 4

The verified table checks every monomial of the unchanged numerical rows.
Codes 0 and 1 both evaluate to the packed seed, so constant terms are retained.

The data come from the unchanged arrays and polynomial rows documented in
`Presentation/source/README.md`. Every numerical equality is checked in Lean's
kernel; the generating Python program is not part of the trusted proof.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair04

lemma steps_check : ∀ n ∈ codes, 2 ≤ n →
    action (if n.testBit 0 then 4 else 0) (table (n / 2)) = table n := by
  apply steps_support
  rw [list_partition]
  simp only [List.append_assoc]
  exact (steps_append check00 (steps_append check01 (steps_append check02 (steps_append check03 (steps_append check04 (steps_append check05 (steps_append check06 (steps_append check07 (steps_append check08 (steps_append check09 (steps_append check10 (steps_append check11 (steps_append check12 (steps_append check13 (steps_append check14 (steps_append check15 (steps_append check16 (steps_append check17 (steps_append check18 (steps_append check19 (steps_append check20 (steps_append check21 (steps_append check22 (steps_append check23 (steps_append check24 (steps_append check25 (steps_append check26 (steps_append check27 (steps_append check28 (steps_append check29 (steps_append check30 (steps_append check31 (steps_append check32 (steps_append check33 (steps_append check34 (steps_append check35 (steps_append check36 (steps_append check37 (steps_append check38 (steps_append check39 (steps_append check40 (steps_append check41 (steps_append check42 (steps_append check43 (steps_append check44 (steps_append check45 (steps_append check46 (steps_append check47 (steps_append check48 (steps_append check49 (steps_append check50 (steps_append check51 (steps_append check52 (steps_append check53 (steps_append check54 (steps_append check55 check56))))))))))))))))))))))))))))))))))))))))))))))))))))))))

lemma row07 : relation MatrixCertificate.NumericalData.row07 = 0 :=
  (relation_eq_table MatrixCertificate.NumericalData.row07 table codes seed_check parent_check steps_check covered07).trans zero07

lemma row08 : relation MatrixCertificate.NumericalData.row08 = 0 :=
  (relation_eq_table MatrixCertificate.NumericalData.row08 table codes seed_check parent_check steps_check covered08).trans zero08

lemma row09 : relation MatrixCertificate.NumericalData.row09 = 0 :=
  (relation_eq_table MatrixCertificate.NumericalData.row09 table codes seed_check parent_check steps_check covered09).trans zero09


end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Pair04
