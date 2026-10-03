module
public import GorensteinWalter.PGammaL2OuterProduct

/-!
# The abelian outer quotient of the projective semilinear group

Over every finite field of odd prime-power order, the derived subgroup of
PGammaL2 lies in the canonical PSL2 range. Consequently that range is normal.
The fields of order three and nine are both included.

The canonical PSL2 range in PGL2 has index two and is preserved by coefficient
automorphisms. On its quotient of order two every coefficient automorphism
fixes both the identity and the unique nonidentity element. Thus the two
coordinates define the homomorphism now shared through PGammaL2OuterProduct
onto the product of PGL2/PSL2 and the field automorphism group. Both factors
are abelian, and its proved kernel is precisely the canonical PSL2 range.

This proves the outer-quotient assertion in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 3 (article page 25). Its pullback supplies
the central-by-abelian commutator bound used to compare Sylow intersections.
The existing large-field normality theorem keeps its public interface.
-/

namespace GorensteinWalter

universe u

public theorem pGammaL2_commutator_le_psl_range
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    commutator (PGammaL2 K) ≤ pGammaL2PSLRange K := by
  let : Fact (IsOddPrimePower (Nat.card K)) := ⟨hK⟩
  let N := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  have hc : Nat.card (PGL2 K ⧸ N) = 2 := pgl2_psl2Range_index_eq_two K hK
  let : CommGroup (PGL2 K ⧸ N) := (isCyclic_of_prime_card hc).commGroup
  let : CommGroup (K ≃+* K) :=
    (finiteField_ringAut_isCyclic_of_oddPrimePower K hK).commGroup
  rw [← pGammaL2OuterProduct_ker K]
  exact Abelianization.commutator_subset_ker (pGammaL2OuterProduct K)

public theorem pGammaL2_psl_range_normal_of_odd_prime_power
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    (pGammaL2PSLRange K).Normal :=
  Subgroup.Normal.of_commutator_le (PGammaL2 K) (pGammaL2_commutator_le_psl_range K hK)

end GorensteinWalter
