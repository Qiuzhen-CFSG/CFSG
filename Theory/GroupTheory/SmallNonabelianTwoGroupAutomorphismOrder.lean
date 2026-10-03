module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderSevenObstruction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFive

/-!
# Sharp odd automorphism orders of small nonabelian two-groups

An odd automorphism subgroup of a nonabelian two-group of order at most32
has order dividing nine when the core has order32, and dividing three
otherwise, provided an order32 core contains one elementary abelian subgroup
of order eight. The witness is required only in the order32 case.

The coarse Frattini linear-group count supplies the three-part bound. The
proved commutator-form arguments exclude seven. A hypothetical factor five
forces core order32 and a central order-two Frattini subgroup; the supplied
elementary eight then contradicts the proved quadratic-form five-exclusion.
The prime-exclusion arithmetic yields the stated sharp order bound.

This is the small-core automorphism bound used in Stellmacher, printed p.42.
No pair of generating eights or quaternion model is assumed.
-/

namespace SmallNonabelianTwoGroup

public theorem small_nonabelian_two_group_odd_order_bound
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32)
    (heights : Nat.card Q = 32 → ∃ elementary : Subgroup Q,
      IsElementaryAbelian 2 elementary ∧ Nat.card elementary = 8)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor)) :
    Nat.card actor ∣ (if Nat.card Q = 32 then 9 else 3) := by
  have hseven := not_seven_dvd_odd_actor_card htwo hnoncomm hbound actor hodd
  have hfive : ¬ 5 ∣ Nat.card actor := by
    intro hdiv
    have hquotient := frattini_quotient_card_eq_sixteen_of_five_dvd
      htwo hnoncomm hbound actor hodd hdiv
    obtain ⟨hQ, hfrattini, _⟩ :=
      frattini_structure_of_quotient_sixteen htwo hnoncomm hbound hquotient
    obtain ⟨elementary, helementary, hcard⟩ := heights hQ
    exact not_five_dvd_odd_actor_card_of_frattini_two htwo hnoncomm hQ hfrattini
      elementary helementary hcard actor hodd hdiv
  exact odd_actor_card_dvd_sharp_of_prime_exclusions htwo hnoncomm hbound actor hodd hfive hseven

end SmallNonabelianTwoGroup
