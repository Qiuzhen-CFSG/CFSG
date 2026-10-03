module
public import Theory.GroupTheory.ElementaryPrimeNormalizer

/-!
# Odd normalizers of order-thirty-one automorphism subgroups

An order-thirty-one subgroup of the automorphism group of a finite
elementary abelian two-group of order thirty-two has odd-order normalizer.
No solvability or specified subgroup model is assumed.

This is the p=31 instance of the general prime-subgroup normalizer theorem.
An involution in the normalizer would have at most two fixed elements by
the transitive prime-cycle argument, whereas its displacement homomorphism
would force 32 to be at most the square of that fixed-subgroup order.
Cauchy's theorem then gives the asserted oddness.

The result is the consequence needed from Parrott, *A characterization of
the Tits' simple group* (1972), the GL(5,2) properties listed on p.673,
property (7). That source gives the stronger order 5*31 description; this
module proves only the oddness needed by the current normalizer argument.
-/

universe u

/-- An order-thirty-one subgroup of Aut(E), for elementary E of order32, has odd normalizer. -/
public theorem odd_card_normalizer_of_elementary_thirtytwo_thirtyone
    (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (K : Subgroup (MulAut E)) (hK : Nat.card K = 31) :
    Odd (Nat.card (Subgroup.normalizer (K : Set (MulAut E)))) := by
  exact odd_card_normalizer_of_elementary_prime 31 (by decide) (by decide) E hE K hK
