module

public import Theory.GroupAction.OddInvariantSylow
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Conjugating invariant p-subgroups into a common invariant subgroup

Suppose a finite two-group A acts by automorphisms on a finite solvable
group K of odd order. Given two A-invariant q-subgroups, an element fixed
by A conjugates the first into an A-invariant q-subgroup that also contains
the second. The supplied action instance is used throughout; neither
elementary Abelianness nor a rank bound on A is required.

Extend the two subgroups to invariant Sylow q-subgroups using the
odd-order invariant Sylow theorem. Their orders and indices make them
Hall subgroups for the singleton prime set. The invariant Hall conjugacy
theorem then gives a conjugating element in C_K(A), and the second Sylow
subgroup is the common overgroup.

This is the local coprime-conjugacy step used in the transitivity argument
for signalizer functors; see Kurzweil–Stellmacher, *The Theory of Finite
Groups*, Section 11.1. Its dependencies are the general invariant Sylow
and Hall conjugacy results in Theory.
-/

private theorem sylow_isHall_singleton
    {K : Type*} [Group K] [Finite K] {q : ℕ} [hq : Fact q.Prime]
    (S : Sylow q K) : IsHallSubgroup {⟨q, hq.out⟩} (S : Subgroup K) := by
  apply isHallSubgroup_of
  · intro r hr
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn] at hr
    have heq : r.val = q := (Nat.prime_dvd_prime_iff_eq r.property hq.out).mp
      (r.property.dvd_of_dvd_pow hr)
    exact Set.mem_singleton_iff.mpr (Subtype.ext heq)
  · intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact S.not_dvd_index

/-- Two invariant q-subgroups of an odd solvable group have a common
invariant q-overgroup after conjugating one by an element fixed by A. -/
public theorem exists_fixedPoint_conj_le_common_invariant_pSubgroup
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    [MulDistribMulAction A K] (hA : IsPGroup 2 A)
    (hKodd : Odd (Nat.card K)) (hKsolv : Group.IsSolvable K)
    {q : ℕ} [Fact q.Prime] (R₁ R₂ : Subgroup K)
    (hR₁ : IsPGroup q R₁) (hR₂ : IsPGroup q R₂)
    (hI₁ : IsInvariant A K R₁) (hI₂ : IsInvariant A K R₂) :
    ∃ c : K, c ∈ fixedPointSubgroup A K ∧
      ∃ E : Subgroup K, IsPGroup q E ∧ IsInvariant A K E ∧
        R₁.map (MulAut.conj c) ≤ E ∧ R₂ ≤ E := by
  obtain ⟨S₁, hRS₁, hS₁I⟩ := exists_invariant_sylow_le_of_isPGroup hA hKodd R₁ hR₁ hI₁
  obtain ⟨S₂, hRS₂, hS₂I⟩ := exists_invariant_sylow_le_of_isPGroup hA hKodd R₂ hR₂ hI₂
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    obtain ⟨n, hn⟩ := hA.exists_card_eq
    rw [hn]
    exact hKodd.coprime_two_left.pow_left n
  obtain ⟨c, hc, heq⟩ := exists_fixedPoint_conj_of_isHallSubgroup_of_isInvariant
    hKsolv hcop {⟨q, Fact.out⟩} (sylow_isHall_singleton S₁) (sylow_isHall_singleton S₂)
    hS₁I hS₂I
  refine ⟨c, hc, S₂, S₂.isPGroup', hS₂I, ?_, hRS₂⟩
  rw [heq]
  exact Subgroup.map_mono hRS₁
