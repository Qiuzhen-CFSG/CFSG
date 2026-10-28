module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.Definitions
public import Theory.SpecificGroups.G2.DoubleCoverInvolutions
public import Theory.GroupTheory.DoubleCoverCentralizer.InvertedDisplacement

/-!
# I.2.2: exceptional central covers

The G₂(4) two-central lifting clause follows from its actual elementary
long-root plane and the double-cover involution argument. The earlier
multiplier conclusion |Z(K)|=2 remains explicit. The other clauses of
I.2.2(5)–(7), including non-two-central lifts, outer inversion and the
sporadic core-square assertions, are not asserted by this module. The
imported displacement theorem proves the algebraic reduction of outer
inversion to its two independent quotient and lifting inputs.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, I.2.2,
printed pp.409–413 / PDF pp.420–424.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
open Subgroup Theory.GroupTheory
variable {K F : Type*} [Group K] [Finite K] [Field F] [Finite F] [CharP F 2]

/-- I.2.2(5a), G₂(4) row, after the earlier center-order calculation. -/
theorem g2_twoCentral_involutions_lift_of_center_card_two
    (e : (K ⧸ center K) ≃* Atlas.G2.Model F) (hF : Nat.card F = 4)
    (hZ : Nat.card (center K) = 2) :
    Atlas.G2.LongRootPlaneLift.CentralInvolutionLifting K :=
  Atlas.G2.DoubleCoverInvolutions.central_involution_lifting e hF hZ

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
