module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates

/-!
# The finite max1 action inequality needed for the J₄ two-rank

The action is the existing direct eleven-coordinate action of the actual
Mathieu quotient Sylow subgroup. For every elementary subgroup B, the product
of its order and the number of common fixed masks must be at most 2¹¹.
Unlike the established characteristicity bound, B need not be normal.
This file specifies the outstanding finite theorem; it does not assert it.

`TwoRank.Reduction` applies precisely this inequality to the aligned image
of an elementary subgroup of an actual J₄ Sylow subgroup. The fixed-mask
convention and ATLAS provenance are in the imported `FixedCoordinates`.
Source application: Aschbacher–Smith G.7.3(2), printed pp.347–348.
-/

@[expose] public section
namespace Janko4.TwoRank
open LocalStructure.SylowCore Simplicity.Max1Fusion.QuotientInvolutions

/-- The finite action inequality, with no normality restriction on B. -/
def ElementaryFixedBound : Prop :=
  ∀ B : Subgroup sylowCandidate, IsElementaryAbelian 2 B →
    Nat.card B * Nat.card (FixedMasks B) ≤ 2048

end Janko4.TwoRank
