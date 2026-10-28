module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderSevenRankThree

/-!
# Order-seven exclusion for small nonabelian two-groups

No odd automorphism subgroup of a nonabelian two-group of order at most32
has order divisible by seven. The faithful Frattini action restricts a
hypothetical seven-factor to quotient order eight or sixteen. The rank-three
argument excludes the former. In the latter the actual characteristic
order-two commutator form gives a nonidentity seventh-order isometry, excluded
by the complete linear obstruction, including its singular-form case.

This is the seven-part of the small-core automorphism bound used in
Stellmacher, printed p.42. No elementary-eight witness is needed for this
prime; that additional hypothesis belongs to the separate five-exclusion.
-/

open scoped IsMulCommutative

namespace SmallNonabelianTwoGroup

public theorem not_seven_dvd_odd_actor_card
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor)) :
    ¬ 7 ∣ Nat.card actor := by
  intro hseven
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  rcases frattini_quotient_card_eight_or_sixteen_of_seven_dvd
      htwo hnoncomm hbound actor hodd hseven with height | hsixteen
  · exact not_seven_dvd_odd_actor_card_of_quotient_eight htwo hnoncomm hbound
      height actor hodd hseven
  · obtain ⟨hdim, form, aut, hform, halt, hne, hpow, hpres⟩ :=
      exists_nontrivial_seven_isometry_of_quotient_sixteen
        htwo hnoncomm hbound hsixteen actor hodd hseven
    exact hne (BinaryAlternatingFour.nonzero_alternating_form_order_seven_eq_one
      hdim form hform halt aut hpow hpres)

end SmallNonabelianTwoGroup
