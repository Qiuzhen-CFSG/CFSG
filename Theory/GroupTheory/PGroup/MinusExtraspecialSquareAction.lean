module

public import Theory.SpecificGroups.MinusExtraspecial.Recognition
public import Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour
public import Theory.GroupTheory.AutomorphismSquareActionTransport

/-!
# Square actions on minus extraspecial groups of order thirty-two

In an extraspecial group of order thirty-two with no elementary abelian
subgroup of order eight, an outer involution given by an inner twist of a
two-power-order automorphism's square fixes an elementary abelian four.
The original automorphism admits an inner correction whose square is the
prescribed involution.

Recognize the group as the quaternion–dihedral central product, apply the
kernel-checked model calculation, and transport both the fixed subgroup and
the correcting element back through the isomorphism. Thus the square root
stays in the prescribed coset modulo inner automorphisms.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace IsExtraspecial

/-- An outer involution which is an inner twist of a square fixes an elementary
four and has a square root in the original coset of inner automorphisms. -/
public theorem square_action_fixed_four_of_card_thirty_two
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]
    (hH : Nat.card H = 32)
    (hrank : ∀ E : Subgroup H, IsElementaryAbelian 2 E → Nat.card E < 8)
    (a b : MulAut H) (p : H) (n : ℕ)
    (hb : b ^ (2 ^ n) = 1) (hab : a = MulAut.conj p * b ^ 2)
    (ha : a ^ 2 = 1) (hout : ¬ ∃ x : H, a = MulAut.conj x) :
    IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id H)) ∧
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id H)) = 4 ∧
    ∃ x : H, (MulAut.conj x * b) ^ 2 = a := by
  obtain ⟨e⟩ := exists_mulEquiv_minusExtraspecial_model hrank hH
  exact e.square_action_fixed_four_transfer
    _root_.MinusExtraspecial.square_action_fixed_four a b p n hb hab ha hout

end IsExtraspecial
