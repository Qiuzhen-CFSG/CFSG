module

public import Theory.SpecificGroups.BabyMonster.Order.Bounds

/-!
# Order comparison for the Baby Monster presentation

A finite upper bound for the fixed `Y₄₃₃` presentation and a verified image
with the matching lower bound determine its order. They also force the map to
that image to be injective, by equality of the finite cardinalities.

The presentation is from Breuer–Magaard–Wilson (2019), §3.1,
https://arxiv.org/abs/1902.07758. The results here are conditional comparison
lemmas: constructing the finite upper bound and the sufficiently large image
remains necessary before asserting finiteness or the order of the carrier.
-/

public section
namespace BabyMonster

/-- A finite upper bound and a matching lower bound from a verified image
determine the order of the fixed presentation. -/
theorem card_eq_of_bounds_and_image [Finite Carrier]
    (hupper : Nat.card Carrier ≤ expectedOrder)
    {G : Type*} [Group G] {t : Generator → G} (h : Relations t)
    (hlower : expectedOrder ≤ Nat.card (Subgroup.closure (Set.range t))) :
    Nat.card Carrier = expectedOrder :=
  hupper.antisymm (hlower.trans (card_generated_le h))

/-- The same bounds prove that the verified representation is faithful. -/
theorem lift_injective_of_bounds_and_image [Finite Carrier]
    (hupper : Nat.card Carrier ≤ expectedOrder)
    {G : Type*} [Group G] {t : Generator → G} (h : Relations t)
    (hlower : expectedOrder ≤ Nat.card (Subgroup.closure (Set.range t))) :
    Function.Injective (lift h) := by
  apply MonoidHom.rangeRestrict_injective_iff.mp
  have hc : Nat.card Carrier ≤ Nat.card (lift h).range := by
    rw [range_lift h]
    exact hupper.trans hlower
  exact ((lift h).rangeRestrict_surjective.bijective_of_nat_card_le hc).injective

end BabyMonster
