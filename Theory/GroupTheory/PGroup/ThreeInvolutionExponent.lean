module

public import Theory.GroupTheory.PGroup.CentralInvolutionExponent

/-!
# Exponent four for groups with three transitive involutions

A finite nonabelian two-group whose three involutions are central and
automorphism-transitive has exponent at most four. This module exposes the
intrinsic exponent theorem for use with the corresponding order calculation.

The structural proof in `CentralInvolutionExponent` first bounds the nilpotency
class by two using a critical subgroup and a fixed-point-free automorphism of
order three. The class-two argument then excludes central elements of order
greater than two and concludes that all fourth powers are trivial.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1,
printed pp.386 and 393. See the imported structural modules for the critical
subgroup and fixed-point-free automorphism arguments.
-/

namespace IsPGroup

/-- A finite nonabelian two-group with three central, automorphism-transitive
involutions has exponent at most four. -/
public theorem exponent_four_of_transitive_three_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ Subgroup.center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y) : ∀ x : P, x ^ 4 = 1 :=
  hP.exponent_four_of_transitive_three_central_involutions
    hnonab hcentral hthree htrans

end IsPGroup
