module

public import Theory.GroupTheory.PrimeRankNonabelianCube

/-!
# Prime rank from a concrete nonabelian subgroup

A subgroup of order `p³` is Sylow when `p⁴` does not divide the ambient
order: the index cannot have a factor p. If that subgroup is nonabelian,
its abelian subgroups are proper and the ambient p-rank is at most two.

This is the subgroup form of the prime-cube argument, useful when explicit
generators construct a small subgroup before the ambient order is known.
See Aschbacher–Smith, Theorem 0.1.2(5), and GLS3 Table 5.3p for its Held
application. No sporadic order or subgroup structure is assumed here.
-/

/-- A concrete nonabelian subgroup of prime-cube order bounds the ambient
prime rank as soon as the next prime power is excluded. -/
public theorem primeRank_le_two_of_nonabelian_subgroup_cube
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hc : Nat.card P = p ^ 3)
    (hna : ¬ IsMulCommutative P) (hfour : ¬ p ^ 4 ∣ Nat.card G) :
    primeRank p G ≤ 2 := by
  have hindex : ¬ p ∣ P.index := by
    intro hd
    apply hfour
    rw [← P.card_mul_index, hc]
    rw [show p ^ 4 = p ^ 3 * p from pow_succ p 3]
    exact Nat.mul_dvd_mul_left (p ^ 3) hd
  exact primeRank_le_two_of_nonabelian_sylow_cube
    ((IsPGroup.of_card hc).toSylow hindex) hc hna
