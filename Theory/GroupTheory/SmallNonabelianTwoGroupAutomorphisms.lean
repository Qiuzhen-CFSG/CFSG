module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrder

/-!
# Odd automorphism subgroups of small nonabelian two-groups

For a nonabelian two-group of order at most32, every odd automorphism
subgroup is elementary abelian at three, and its order divides nine at core
order32 or three otherwise. At order32 a single elementary-eight subgroup
is required, exactly as in the sharp order theorem.

The sharp order bound excludes primes five and seven using the actual
Frattini quadratic and commutator forms. The remaining possible order-nine
actor cannot be cyclic by the proved faithful-action orbit count, so its
exponent divides three. This completes the generic automorphism input for
the small-index local quotient argument in Stellmacher (8.6), printed p.42.
-/

namespace SmallNonabelianTwoGroup

public theorem small_nonabelian_two_group_odd_automorphisms
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32)
    (heights : Nat.card Q = 32 → ∃ elementary : Subgroup Q,
      IsElementaryAbelian 2 elementary ∧ Nat.card elementary = 8)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor)) :
    IsElementaryAbelian 3 actor ∧
      Nat.card actor ∣ (if Nat.card Q = 32 then 9 else 3) := by
  have hcard := small_nonabelian_two_group_odd_order_bound htwo hnoncomm hbound heights actor hodd
  refine ⟨elementaryAbelian_of_card_dvd_nine htwo hbound actor (hcard.trans ?_), hcard⟩
  split_ifs <;> norm_num

end SmallNonabelianTwoGroup
