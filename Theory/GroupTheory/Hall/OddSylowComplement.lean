module

public import Theory.GroupTheory.Hall.Existence
public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.Group.PUnit

/-!
# An odd complement to a supplied Sylow two-subgroup

Every Sylow two-subgroup of a finite solvable group admits an odd-order
complement. The theorem keeps the supplied Sylow subgroup and concludes
`IsComplement'`, so multiplication gives a unique factorization of every
group element as a Sylow element followed by a complement element. Neither
subgroup is assumed normal.

Hall existence, applied with the trivial unit-group action, provides a Hall
subgroup for the primes different from two. Its order is coprime to the
Sylow order, and its index is coprime to the Sylow index. Subgroup and index
divisibility therefore identify its order with the Sylow index. The resulting
cardinality product and coprimality give the exact complement relation.

This is the standard complementary-Hall-subgroup consequence of Hall's
theorem. It supplies the literal product factorization needed for the local
factor in Stellmacher's (6.1), using only the general Hall development.
-/

namespace Subgroup

public theorem exists_odd_complement_sylow_two
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (S : Sylow 2 G) :
    ∃ U : Subgroup G, Odd (Nat.card U) ∧ (S : Subgroup G).IsComplement' U := by
  classical
  let _ : MulDistribMulAction Unit G := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  obtain ⟨U, hUHall, _⟩ := exists_isHallSubgroup_isInvariant
    (G := G) (A := Unit) hsolv (by simp) {p : Nat.Primes | p.val ≠ 2}
  have hUtwo : ¬ 2 ∣ Nat.card U := by
    intro h
    exact hUHall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h rfl
  have hUodd : Odd (Nat.card U) := by
    rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hcop_cards : Nat.Coprime (Nat.card U) (Nat.card S) := by
    rw [hn]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hUtwo).symm.pow_right n
  have hcop_indices : Nat.Coprime (S : Subgroup G).index U.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpS hpU
    have hp2 : p = 2 := by
      exact Classical.not_not.mp (hUHall.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpU)
    exact S.not_dvd_index (hp2 ▸ hpS)
  have hcard_dvd_index : Nat.card U ∣ (S : Subgroup G).index := by
    have hdvd : Nat.card U ∣ (S : Subgroup G).index * Nat.card S := by
      simpa only [index_mul_card] using card_subgroup_dvd_card U
    exact hcop_cards.dvd_of_dvd_mul_right hdvd
  have hindex_dvd_card : (S : Subgroup G).index ∣ Nat.card U := by
    have hdvd : (S : Subgroup G).index ∣ Nat.card U * U.index := by
      simpa only [card_mul_index] using (S : Subgroup G).index_dvd_card
    exact hcop_indices.dvd_of_dvd_mul_right hdvd
  have hcardU : Nat.card U = (S : Subgroup G).index :=
    Nat.dvd_antisymm hcard_dvd_index hindex_dvd_card
  refine ⟨U, hUodd, isComplement'_of_coprime ?_ hcop_cards.symm⟩
  rw [hcardU]
  exact (S : Subgroup G).card_mul_index
end Subgroup
