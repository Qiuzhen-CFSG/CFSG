module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.Construction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.FourCoordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus.DiagonalCentralizer

/-!
# The controlled odd-torus route to inner-family generation

For prime fields of order greater than three and congruent to three modulo
four, simultaneous four-group coordinates and diagonal centralizer control
give a split torus normalized by the full original C_T(A). An odd prime-order
unit supplies a literal odd subgroup whose commutator with A contains the
required mixing matrix. Both geometric inputs are discharged here, and the
published generation reduction applies the result to the original family
actor. No strongly-quasithin hypothesis is needed for this construction.

Source: Aschbacher--Smith E.1.2, E.1.5 and E.1.14(7), printed
pp.209--210,214, and Aschbacher (1982), Lemma 4.11.
-/

public section
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
open InnerGenerationGeometry

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

namespace InnerGenerationGeometry

/-- The full original Sylow centralizer normalizes an odd-prime subgroup
whose commutator with the given inner four-group contains an actual mixing
matrix. The residue condition already implies that the field order is odd. -/
theorem fourGroupOddMixing_of_card_mod_four_eq_three {p : ℕ}
    (hp : p.Prime) (hbig : 3 < p) (hF : Nat.card F = p) (hp4 : p % 4 = 3) :
    FourGroupOddMixing F := by
  exact OddTorus.fourGroupOddMixing_of_diagonalTwoControl F hp hbig hF hp4
    (OddTorus.diagonalTwoControl F hF hp4)

end InnerGenerationGeometry

/-- The torus construction feeds the original inner-family generation
consumer, with its two geometric inputs explicit. -/
theorem innerCentralizerGeneration_of_odd_torus_inputs {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hbig : 3 < p)
    (hF : Nat.card F = p) (hp4 : p % 4 = 3)
    (hcoords : OddTorus.FourGroupCoordinates F)
    (hcontrol : OddTorus.DiagonalTwoControl F) : InnerCentralizerGeneration F := by
  exact innerCentralizerGeneration_of_four_group_odd_mixing F hp ho hF
    (OddTorus.fourGroupOddMixing_of_inputs F hp hbig hF hp4 hcoords hcontrol)

/-- The residue-three odd-torus construction discharges the mixing premise
of the original inner-family generation consumer. -/
theorem innerCentralizerGeneration_of_odd_torus {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hbig : 3 < p)
    (hF : Nat.card F = p) (hp4 : p % 4 = 3) : InnerCentralizerGeneration F := by
  exact innerCentralizerGeneration_of_four_group_odd_mixing F hp ho hF
    (fourGroupOddMixing_of_card_mod_four_eq_three F hp hbig hF hp4)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
