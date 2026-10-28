module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveSquare
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadratic

namespace SmallNonabelianTwoGroup

open scoped IsMulCommutative

public theorem not_five_dvd_odd_actor_card_of_frattini_two
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hQ : Nat.card Q = 32) (hfrattini : Nat.card (frattini Q) = 2)
    (elementary : Subgroup Q) (helementary : IsElementaryAbelian 2 elementary)
    (helementaryCard : Nat.card elementary = 8)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor)) :
    ¬ 5 ∣ Nat.card actor := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  let : IsElementaryAbelian 2 (frattini Q) := frattini_two_elementary hfrattini
  let quotientAction := (Subgroup.quotientAut (frattini Q)).comp actor.subtype
  have hcard : Nat.card actor = Nat.card quotientAction.range :=
    Nat.card_congr (Equiv.ofInjective quotientAction
      (odd_frattini_action_injective htwo actor hodd))
  rw [hcard]
  apply not_five_dvd_quadratic_preserving_actor_card
    (frattini_quotient_card_sixteen_of_card_thirty_two hQ hfrattini) hfrattini
    (frattiniSquare htwo hfrattini) (frattiniPolar htwo hfrattini)
    (frattiniSquare_one htwo hfrattini)
    (frattiniSquare_mul htwo hfrattini)
    (frattiniPolar_mul_left htwo hfrattini)
    (frattiniPolar_nonzero htwo hfrattini hnoncomm)
    (elementary.map (QuotientGroup.mk' (frattini Q)))
    (elementary_image_frattini_card_ge_four hfrattini elementary helementaryCard)
    (elementary_image_frattini_singular htwo hfrattini elementary helementary)
    quotientAction.range
  intro aut haut vector
  obtain ⟨original, rfl⟩ := haut
  exact frattiniSquare_invariant htwo hfrattini original.val vector

end SmallNonabelianTwoGroup
