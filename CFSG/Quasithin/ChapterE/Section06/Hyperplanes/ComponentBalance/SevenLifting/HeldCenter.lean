module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.HeldCenterSource
public import Theory.SpecificGroups.Held.CentralCovers.OddCenter

/-!
# The E.6.18 exclusion with the Held center input discharged

Apply the finite quasisimple Held-cover theorem to the original ambient
seven-component exclusion. The complete catalogue inspection and the
literal central quotient are those of `HeldCenterSource`; the hypotheses
E.6.1 and E.6.15 and the original elementary abelian subgroup are retained.

Source: Aschbacher--Smith E.6.18, printed p.252, and I.1.3, printed p.407.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
universe u

/-- The original E.6.18 seven exclusion for the full known-simple catalogue. -/
theorem sevenExcluded_knownSimple
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (h15 : HypothesisE615 V) :
    Enlargement.SevenExcluded M V :=
  sevenExcluded_of_held_center (fun _ _ _ _ => Held.CentralCovers.odd_center) h h15

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
