module

public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder

/-!
# Orders and Sylow markings of the concrete Tits parabolics

The existing presentation and coset calculations give the orders of the two
overgroups. Restricting the ambient certified Sylow subgroup gives the local
Sylow markings, of indices five and three. These facts determine their entire
intersection in `Geometry` without another permutation enumeration.

Source: Parrott (1972), pp. 672 and 683; Aschbacher--Smith F.1.11--12,
printed pp. 262--264. These are full-parabolic orders, not the disputed
first-core order printed in F.1.12(I)(9).
-/

@[expose] public section
namespace Tits.ExceptionalParabolics

theorem first_card : Nat.card first = 10240 := ReeLocalBlockOrders.first_card

theorem second_card : Nat.card second = 6144 := RelativeSecondBlockLayers.second_card

/-- The ambient Sylow marking restricted to the first full parabolic. -/
def firstSylowTwo : Sylow 2 first :=
  atlas1600SylowTwo.subtype (by simpa only [atlas1600SylowTwo_coe] using sylow_le_first)

theorem firstSylowTwo_coe :
    (firstSylowTwo : Subgroup first) = S.subgroupOf first := by
  rw [firstSylowTwo, Sylow.coe_subtype, atlas1600SylowTwo_coe]

theorem first_sylow_index : (S.subgroupOf first).index = 5 := by
  have hs : Nat.card (S.subgroupOf first) = 2048 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylow_le_first).toEquiv).trans sylow_card
  have h := (S.subgroupOf first).card_mul_index
  rw [hs, first_card] at h
  omega

/-- The ambient Sylow marking restricted to the second full parabolic. -/
abbrev secondSylowTwo : Sylow 2 second := RelativeSecondBlockLayers.secondSylowTwo

theorem secondSylowTwo_coe :
    (secondSylowTwo : Subgroup second) = S.subgroupOf second :=
  RelativeSecondBlockLayers.secondSylowTwo_coe

theorem second_sylow_index : (S.subgroupOf second).index = 3 :=
  RelativeSecondBlockLayers.second_sylow_index

end Tits.ExceptionalParabolics
