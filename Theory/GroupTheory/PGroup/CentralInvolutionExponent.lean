module

public import Theory.GroupTheory.PGroup.ThreeInvolutionClassTwo
public import Theory.GroupTheory.PGroup.ClassTwoThreeInvolutionExponent

/-!
# Exponent four from three transitive central involutions

A finite nonabelian two-group with exactly three central involutions, on
which its automorphism group acts transitively, has exponent at most four.

The critical subgroup argument first gives nilpotency class at most two.
The class-two exponent theorem then rules out a center of exponent greater
than two: central square roots would force the nontrivial derived subgroup
to be cyclic, contradicting transitivity on the three involutions.

This assembles the elementary structure reduction used in the
three-involution problem of Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3
and Lemma 5.1. The class bound uses Thompson's critical subgroup theorem and
Neumann's fixed-point-free automorphism theorem; see the imported modules
for the individual arguments and their sources.
-/

namespace IsPGroup

/-- A finite nonabelian two-group with exactly three central involutions and
an automorphism group transitive on them has exponent at most four. -/
public theorem exponent_four_of_transitive_three_central_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ Subgroup.center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y) : ∀ x : P, x ^ 4 = 1 :=
  hP.exponent_four_of_class_two_of_transitive_three_involutions
    hnonab hcentral hthree htrans
    (hP.commutator_le_center_of_three_transitive_involutions hcentral hthree htrans)

end IsPGroup
