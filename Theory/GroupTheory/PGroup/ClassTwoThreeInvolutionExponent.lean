module

public import Theory.GroupTheory.PGroup.ClassTwoSquareClasses
public import Theory.GroupTheory.PGroup.ClassTwoCyclicDerived

/-!
# Exponent four from class two and three transitive central involutions

A nonabelian finite two-group with central, automorphism-transitive
involutions, exactly three involutions, and central derived subgroup has
exponent at most four.

If the center has exponent at most two, central commutators imply that all
squares are central, giving the conclusion. Otherwise transitivity gives a
central square root for every involution. Squaring then embeds first omega
of the central quotient into the center modulo squares, bounding its order
by four. The abelian central quotient has at most two generators, so the
derived subgroup is cyclic. This contradicts transitivity: the nontrivial
characteristic derived subgroup must contain all three involutions.

This proves only the exponent reduction under an explicit class-two
hypothesis. It is the elementary reduction used in the three-involution
structure problem of Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3 and
Lemma 5.1; no classification theorem or class bound is assumed implicitly.
-/

namespace IsPGroup

/-- Three transitive central involutions in a nonabelian finite two-group of
class at most two force every fourth power to be the identity. -/
public theorem exponent_four_of_class_two_of_transitive_three_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ Subgroup.center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hclass : commutator P ≤ Subgroup.center P) : ∀ x : P, x ^ 4 = 1 := by
  rcases hP.center_exponent_two_or_involutions_have_central_square_roots htrans with
    hZ | hroots
  · exact exponent_four_of_class_two_of_center_exponent_two hclass hZ
  · have hbound := card_omega_center_quotient_le_of_central_square_roots
      hclass hcentral hroots
    rw [card_omega_center_eq_four_of_three_central_involutions hcentral hthree] at hbound
    exact (hP.not_isCyclic_commutator_of_transitive_three_involutions
      hnonab hthree htrans
      (hP.isCyclic_commutator_of_card_omega_center_quotient_le_four hclass hbound)).elim

end IsPGroup
