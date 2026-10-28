module

public import Theory.GroupTheory.CyclicTwoSubgroups
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Cardinality detects inclusion among cyclic two-subgroups

Subgroups of a cyclic group of two-power order form a chain: they are generated
by successive two-power powers of a generator. Consequently, their cardinality
ordering implies inclusion. The exact order of the supplied generator is not
needed, only that a power of two annihilates it.

This extends the subgroup description in `CyclicTwoSubgroups`. One application
is the comparison of fixed subgroups in Aschbacher--Smith, 16.3.12, printed
pp.1181--1182.
-/

namespace Subgroup

/-- Cardinality ordering implies inclusion for subgroups of a cyclic two-group. -/
public theorem le_of_card_le_of_le_zpowers_two_pow {G : Type*} [Group G] [Finite G] {y : G} {n : ℕ}
    (hy : y ^ (2 ^ n) = 1) (H K : Subgroup G)
    (hH : H ≤ zpowers y) (hK : K ≤ zpowers y)
    (hcard : Nat.card H ≤ Nat.card K) : H ≤ K := by
  obtain ⟨i, _, rfl⟩ := eq_zpowers_two_pow_of_le hy H hH
  obtain ⟨j, _, rfl⟩ := eq_zpowers_two_pow_of_le hy K hK
  have hle : ∀ i j : ℕ, i ≤ j → zpowers (y ^ (2 ^ j)) ≤ zpowers (y ^ (2 ^ i)) := by
    intro i j hij
    apply zpowers_le_of_mem
    have he : j = i + (j - i) := (Nat.add_sub_of_le hij).symm
    rw [he, pow_add, pow_mul]
    exact pow_mem (mem_zpowers _) _
  rcases le_total i j with hij | hji
  · exact (eq_of_le_of_card_ge (hle i j hij) hcard).ge
  · exact hle j i hji

end Subgroup
