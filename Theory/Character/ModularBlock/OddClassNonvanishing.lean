module

public import Theory.Character.ModularBlock.Congruence

/-!
# Principal-block characters on odd conjugacy classes

A character in the principal congruence two-block cannot vanish on a
conjugacy class of odd cardinality. Its central character has the same
reduction as the class cardinality, which is one modulo the prime above two.
This is the elementary central-character criterion used to exhaust the
principal block in the semidihedral section calculation (ABG III.5--6).
-/

namespace ModularBlock.PrincipalBlockConstruction
open ModularBlock.BlockPreliminaries

variable {G : Type*} [Group G] [Finite G]

/-- Every principal-block character is nonzero on a class of odd size. -/
public theorem PrincipalCongruenceBlockData.character_ne_zero_of_odd_class
    (d : PrincipalCongruenceBlockData G) (i : d.I) (hi : i ∈ d.block)
    (c : ConjClasses G) (hc : Odd (Nat.card c.carrier)) : d.chi i c ≠ 0 := by
  let : Nontrivial ((cyclotomicOrder d.eta) ⧸ d.primeIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr d.primeIdeal_maximal.ne_top
  have h := congrFun ((d.mem_block_iff i).mp hi) c
  change Ideal.Quotient.mk d.primeIdeal
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) (d.complete.1 i) c) =
    Ideal.Quotient.mk d.primeIdeal
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi d.principal)
        (d.complete.1 d.principal) c) at h
  have hp : centralCharacterInCyclotomicOrder d.eta_spec (d.chi d.principal)
      (d.complete.1 d.principal) c = (Nat.card c.carrier : cyclotomicOrder d.eta) := by
    apply Subtype.ext
    simp [centralCharacterInCyclotomicOrder, ordinaryCentralCharacterValue, d.principal_eq]
  have ho : Ideal.Quotient.mk d.primeIdeal
      (Nat.card c.carrier : cyclotomicOrder d.eta) = 1 := by
    obtain ⟨n, hn⟩ := hc
    rw [hn]
    push_cast
    simp [d.two_eq_zero_mod_primeIdeal]
  rw [hp, ho] at h
  intro hz
  have hz' : centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
      (d.complete.1 i) c = 0 := by
    apply Subtype.ext
    simp [centralCharacterInCyclotomicOrder, ordinaryCentralCharacterValue, hz]
  rw [hz', map_zero] at h
  exact zero_ne_one h

end ModularBlock.PrincipalBlockConstruction
