module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.Seventh
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryAssembly

/-!
# The odd marked M₁ relations in finite perfect central double covers

The seventh word lies in the central binary kernel. A common twist by its
value satisfies the twelve local relators; the local order bound supplies
a section, and the checked Schreier parity identity forces that twist to be
trivial. Reflection compatibility and the mapped ninth-word certificate then
prove the other two odd equations. All four even-image premises are retained.

`binaryOddRelations` supplies the exact conditional contract. Its actual
application to `odd_center_of_binary_m1` leaves only `BinaryEvenRelations`
explicit. The final owner `qt-held-odd-center` supplies that independent
producer and completes the Chapter E and Chapter 12 source applications.

Sources: John Bray's `Held/Model/Source/HeG1-P1.M`, the frozen marked words in
`M1Restriction/Data.lean`, and Aschbacher--Smith I.1.3, p.407.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open PerfectCentralCovering Subgroup.CosetWordCertificate Theory.GroupTheory
universe u

/-- The three odd marked equations, conditional only on the original four
even equations in the same finite perfect central double cover. -/
theorem binaryOddRelations : BinaryOddRelations.{u} := by
  intro E _ _ f hcard h ht heven
  exact BinaryOdd.image_odd_of_even_and_seven f h ht heven
    (BinaryOdd.image_seven_of_even f hcard h ht heven)

/-- Application supplying the proved odd contract to the actual Held-center
assembly, retaining the independent even producer explicitly. -/
theorem odd_center_of_binary_even (heven : BinaryEvenRelations.{u})
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (e : (X ⧸ Subgroup.center X) ≃* He) : Odd (Nat.card (Subgroup.center X)) :=
  odd_center_of_binary_m1 heven binaryOddRelations e

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
