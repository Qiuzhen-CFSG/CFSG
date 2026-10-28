module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.SplitMonomial.Index
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.SplitMonomial.Transport

/-!
# Solvable full-Sylow mixing in the split residue class

For a finite field of cardinality one modulo four, the split monomial
subgroup with inverse transpose adjoined has odd relative index in the
standard involution centralizer. Sylow conjugacy within that centralizer
puts any prescribed full ambient Sylow in a conjugate of this solvable
overgroup. The orthogonal signed swap supplies the mixing matrix, and the
transport retains a literal determinant-one coordinate conjugator.

This proves the split witness contract and applies it to the published
inner-centralizer generation consumer. In particular it covers the source
prime fields with p > 3 and p congruent to one modulo four.
Source: Aschbacher--Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209--210,
214; Aschbacher (1982), Lemma 4.11.
-/

public section
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

namespace InnerGenerationGeometry

/-- A field of order one modulo four supplies the full solvable mixing contract. -/
theorem solvableMixing_of_card_mod_four_eq_one (hmod : Nat.card F % 4 = 1) :
    SolvableMixing F := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  exact solvableMixing_of_splitMonomial_odd_relIndex F hodd
    (splitMonomial_odd_relIndex F hodd hmod)

end InnerGenerationGeometry

/-- The split construction discharges the solvable-overgroup premise of the
actual inner-centralizer generation reduction. -/
theorem innerCentralizerGeneration_of_card_mod_four_eq_one (hmod : Nat.card F % 4 = 1) :
    InnerCentralizerGeneration F :=
  innerCentralizerGeneration_of_solvable_mixing F
    (InnerGenerationGeometry.solvableMixing_of_card_mod_four_eq_one F hmod)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
