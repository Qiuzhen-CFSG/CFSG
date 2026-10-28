module
public import Theory.SpecificGroups.Tits.ThreeRank
public import Theory.GroupTheory.OddPrimeRankOneSylow
/-!
# The lower three-rank bound for the concrete Tits group

The certified nonabelian subgroup of order 27 cannot have odd prime rank at
most one: that bound would make it cyclic. Its inclusion into Atlas1600Group
therefore gives three-rank at least two. This complements the existing upper
bound using only the already checked words, not an additional order certificate.

Source: Parrott (1972), §5, p.683; the nonabelian three-subgroup is constructed
in `Theory.SpecificGroups.Tits.ThreeRank`.
-/

public section
namespace Tits.ThreeRank
open Subgroup Theory.GroupTheory

theorem rank_two_le : 2 ≤ primeRank 3 Atlas1600Group := by
  by_contra hn
  have hr : primeRank 3 Atlas1600Group ≤ 1 := by omega
  have hrS : primeRank 3 sylowSubgroup ≤ 1 :=
    (primeRank_le_of_injective 3 sylowSubgroup.subtype Subtype.val_injective).trans hr
  have hp : IsPGroup 3 sylowSubgroup := IsPGroup.of_card (n := 3) sylowSubgroup_card
  have hc : IsCyclic sylowSubgroup := by
    apply hp.isCyclic_of_odd_of_elementary_card_le (by decide)
    intro E hE
    let := hE
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hrS E
  let := hc
  exact sylowSubgroup_nonabelian inferInstance

end Tits.ThreeRank
