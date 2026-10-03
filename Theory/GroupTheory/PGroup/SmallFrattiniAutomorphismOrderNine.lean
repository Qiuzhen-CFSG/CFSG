module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismReduction
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Small Frattini quotients exclude automorphisms of order nine

A finite two-group whose Frattini quotient has at most sixteen elements
has no automorphism of order nine. The Frattini automorphism kernel is a
two-group, so passage to the quotient preserves an odd automorphism order.

The remaining obstruction is the counting argument already proved in
`SmallNonabelianTwoGroup.not_isCyclic_of_card_nine_of_faithful` (in fact,
for two-groups of order at most thirty-two). A cyclic group of order nine
acts freely outside the fixed subgroup of its subgroup of order three.
The size of this complement must be divisible by nine, which is incompatible
with the possible orders of the group and its proper fixed subgroup.

Sources: the counting proof in
`Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismReduction` and the
Burnside basis kernel theorem in
`Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel`.
-/

namespace IsPGroup

private theorem orderOf_mulAut_ne_nine_of_card_le_thirtytwo
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hcard : Nat.card G ≤ 32) (a : MulAut G) : orderOf a ≠ 9 := by
  intro ha
  let A := Subgroup.zpowers a
  have hA : Nat.card A = 9 := (Nat.card_zpowers a).trans ha
  have hfaith : fixingSubgroup A (Set.univ : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    intro element hfix
    apply Subtype.ext
    apply MulEquiv.ext
    intro point
    rw [mem_fixingSubgroup_iff] at hfix
    exact hfix point (Set.mem_univ point)
  exact SmallNonabelianTwoGroup.not_isCyclic_of_card_nine_of_faithful
    hA hG hcard hfaith inferInstance

/-- A finite two-group with Frattini quotient of order at most sixteen
has no automorphism of order nine. -/
public theorem orderOf_mulAut_ne_nine_of_card_frattini_quotient_le_sixteen
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hcard : Nat.card (Q ⧸ frattini Q) ≤ 16) (a : MulAut Q) :
    orderOf a ≠ 9 := by
  intro ha
  let f := Subgroup.quotientAut (frattini Q)
  have horder : orderOf (f a) = 9 := by
    rw [f.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (Subgroup.isPGroup_quotientAut_frattini_kernel hQ) a (by rw [ha]; decide), ha]
  exact orderOf_mulAut_ne_nine_of_card_le_thirtytwo
    (hQ.to_quotient (frattini Q)) (by omega) (f a) horder

end IsPGroup
