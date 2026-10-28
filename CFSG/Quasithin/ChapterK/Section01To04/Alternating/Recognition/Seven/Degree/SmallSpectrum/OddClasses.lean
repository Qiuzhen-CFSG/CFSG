module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum.Inputs
public import Theory.SpecificGroups.AlternatingSeven.OddConjugacyClasses

/-!
# The odd-order class bound for the binary A₇ spectrum

The permutation cycle-type proof gives at most six odd-order conjugacy classes
of the actual A₇. This discharges the literal class-count premise of
`sevenSmallDegreeSpectrum_of_constructions`; the construction of the candidate
modules remains with that theorem's assembly owner.

Source context: Aschbacher–Smith, K.1.2, printed p.452/PDF p.463, and its
supporting characteristic-two degree list `1, 4, 4, 6, 14, 20`.
-/

public section

namespace CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum

/-- The class-count input for exhaustion of the six binary A₇ candidates. -/
theorem odd_class_count_le_six :
    Nat.card (ConjClasses.mk '' {g : alternatingGroup (Fin 7) | ¬ 2 ∣ orderOf g}) ≤ 6 :=
  alternatingGroup.SevenOddConjugacyClasses.odd_class_count_le_six

end CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum
