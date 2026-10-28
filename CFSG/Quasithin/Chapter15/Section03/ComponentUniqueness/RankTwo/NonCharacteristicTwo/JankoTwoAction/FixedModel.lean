module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Models
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction

/-!
# Fixed Aut(J₂) calculation and the residual convention

The intrinsic construction uses exactly the inner image of `Seed.q₂` in
`Models`, and its full normalizer. The index-defined Stellmacher residual
agrees with the embedded intrinsic p-residual. The actual radical lies in
that residual. The checked radical fixer and cubic action prove that the
full normalizer's two-core center has at most four elements and that its
two-residual has trivial centralizer in all automorphisms.

Source: Aschbacher--Smith 15.3.42, final paragraph, printed p.1138;
GLS3 Table 5.3g. No ambient local marking or component placement is used.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction.FixedModel
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction

/-- The source's finite-index residual is the intrinsic residual on the same subgroup. -/
theorem secondResidual_eq_fullResidual : secondResidual = fullResidual :=
  ComponentIntersection.twoResidualAmbient_eq_map_pResidual secondNormalizer

/-- The actual inner radical lies in the full normalizer's two-residual. -/
theorem secondRadical_le_secondResidual : secondRadical ≤ secondResidual := by
  rw [secondResidual_eq_fullResidual]
  exact innerRadical_le_fullResidual

/-- The center-bound reduction through the actual radical fixer. -/
theorem radical_center_card_le_of_radical_centralizer
    (hc : centralizer (secondRadical : Set Model) ≤ secondRadical) :
    Nat.card (center (secondNormalizer.pCoreIn 2)) ≤ 4 :=
  core_center_card_le_of_radical_centralizer hc

/-- The centralizer reduction through the actual radical fixer. -/
theorem residual_centralizer_eq_bot_of_radical_centralizer
    (hc : centralizer (secondRadical : Set Model) ≤ secondRadical) :
    centralizer (secondResidual : Set Model) = ⊥ := by
  rw [secondResidual_eq_fullResidual]
  exact NormalizerAction.residual_centralizer_eq_bot_of_radical_centralizer hc

/-- The fixed full automorphism normalizer's two-core center has order at most four. -/
theorem radical_center_card_le : Nat.card (center (secondNormalizer.pCoreIn 2)) ≤ 4 :=
  NormalizerAction.core_center_card_le

/-- The fixed Stellmacher two-residual has trivial centralizer in the full model. -/
theorem residual_centralizer_eq_bot : centralizer (secondResidual : Set Model) = ⊥ := by
  rw [secondResidual_eq_fullResidual]
  exact NormalizerAction.residual_centralizer_eq_bot

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction.FixedModel
