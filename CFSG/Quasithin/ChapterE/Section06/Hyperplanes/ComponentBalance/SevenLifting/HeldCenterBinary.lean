module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.HeldCenterSource
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryAssembly

/-!
# The E.6.18 consumer of the two remaining Held word families

The concrete model inspection is already established in `HeldCenterSource`.
Here its final cover-center input follows from the even and odd marked-word
contracts for actual perfect central double covers. Both contracts remain
explicit and must be proved before this becomes an unconditional source result.
All ambient hypotheses and quotient conventions are inherited unchanged.

Source: Aschbacher--Smith E.6.18, p.252, and I.1.3, p.407.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
open Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
universe u

/-- The actual E.6.18 application of the marked double-cover word reduction. -/
theorem sevenExcluded_of_held_binary_m1
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M V : Subgroup G}
    (heven : BinaryEvenRelations.{u}) (hodd : BinaryOddRelations.{u})
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (h15 : HypothesisE615 V) :
    Enlargement.SevenExcluded M V := by
  apply sevenExcluded_of_held_center _ h h15
  intro X _ _ _ ⟨e⟩
  exact odd_center_of_binary_m1 heven hodd e

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
