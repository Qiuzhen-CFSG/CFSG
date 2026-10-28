module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.PGroup

/-!
# Automorphisms of cyclic two-groups

A finite cyclic two-group has a two-group of automorphisms. The cardinality
of its automorphism group is the Euler totient of its order. For order
2^(n+1), that totient is 2^n; the trivial group has one automorphism.

This elementary restriction on automorphisms is used in the centric subgroup
reduction for ABG Chapter II, Section 1, Proposition 1, article pages 10–11
of `refs/latex/alperin-brauer-gorenstein.tex`. It is stated independently of
the ABG campaign and uses only Mathlib cardinality and p-group APIs.
-/

namespace IsPGroup
/-- The automorphism group of a finite cyclic two-group is a two-group. -/
public theorem mulAut_of_isCyclic_two {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hG : IsPGroup 2 G) : IsPGroup 2 (MulAut G) := by
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  cases n with
  | zero =>
    apply IsPGroup.of_card (n := 0)
    rw [IsCyclic.card_mulAut, hn]
    norm_num
  | succ n =>
    apply IsPGroup.of_card (n := n)
    rw [IsCyclic.card_mulAut, hn, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
end IsPGroup
