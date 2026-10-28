module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven.Eleven
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryAssembly

/-!
# The four even marked M₁ relations in central double covers of Held

The source involution and the square of the source centralizing word have
square-one lifts. Concrete conjugacies transfer this to the segment words
in entries 4, 6 and 11. Two squares give the first two entries, and seven
segment reversals give entry 11. Entry 10 is a commutator whose odd-order
factor forces commutation through the central binary kernel.

This proves the exact even-word contract without assuming presentation
faithfulness, the multiplier, or triviality of the cover. The application to
`BinaryAssembly.odd_center_of_binary_m1` retains `BinaryOddRelations`;
its final discharge belongs to `qt-held-odd-center`. Thus this module
completes the even family, not the unconditional odd-center theorem.

Sources: John Bray's `Held/Model/Source/HeG1-P1.M`, the frozen marked words
in `M1Restriction/Data.lean`, and Aschbacher--Smith I.1.1 and I.1.3, p.407.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open PerfectCentralCovering Theory.GroupTheory
universe u

/-- The four literal even relations hold under the exact compatible marking
in every finite perfect central double cover. -/
theorem binaryEvenRelations : BinaryEvenRelations.{u} := by
  intro E _ _ f hc h ht i hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact BinaryEven.relation_four f hc h ht
  · exact BinaryEven.relation_six f hc h ht
  · exact BinaryEven.relation_ten f hc h ht
  · exact BinaryEven.relation_eleven f hc h ht

/-- Supplying the even producer leaves precisely the existing odd-word
producer as the Held-cover assembly premise. -/
theorem odd_center_of_binary_odd (hodd : BinaryOddRelations.{u})
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (e : (X ⧸ Subgroup.center X) ≃* He) : Odd (Nat.card (Subgroup.center X)) :=
  odd_center_of_binary_m1 binaryEvenRelations hodd e

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
