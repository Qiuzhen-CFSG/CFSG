module

public import Theory.GroupTheory.PrimeRankNonabelianCube
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.Mathieu.M12.Properties.Sylow3
public import Theory.Mathieu.M24.Properties.Sylow3

/-!
# Ordinary three-rank bounds for M12 and M24

The concrete Sylow 3-subgroups have order 27 and are nonabelian. Their
three-ranks are at most two by the prime-cube order bound; Sylow conjugacy
transfers the bounds to the ambient Witt-design automorphism groups.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, Theorem 0.1.2(5), printed p.4, repeated on p.482.
-/

namespace Sporadic.Mathieu

public theorem m12_primeRank_three_le_two : primeRank 3 M12 ≤ 2 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [m12Sylow3.primeRank_eq]
  apply primeRank_le_two_of_nonabelian_card_cube
  · change Nat.card m12Sylow3Subgroup = 3 ^ 3
    simpa using m12Sylow3Subgroup_card
  · exact m12Sylow3Subgroup_isNonabelian

public theorem m24_primeRank_three_le_two : primeRank 3 M24 ≤ 2 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [m24Sylow3.primeRank_eq]
  apply primeRank_le_two_of_nonabelian_card_cube
  · change Nat.card m24Sylow3Subgroup = 3 ^ 3
    simpa using m24Sylow3Subgroup_card
  · exact m24Sylow3Subgroup_isNonabelian

end Sporadic.Mathieu
