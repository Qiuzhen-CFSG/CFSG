module

public import Stellmacher.MainDefs

/-!
# The all-prime N condition

An N-group has solvable normalizers of every nontrivial p-subgroup for every
prime p. This is Thompson's original all-prime local-solvability condition;
it is independent of any proposed classification or model catalogue.
Specializing to p=2 gives the existing N2 condition used in Stellmacher's
local classification. The witness in IsTwoLocal is the same subgroup Q,
so the specialization requires no normalizer transfer or added hypothesis.

Source: Thompson's N-group theorem, as quoted in the introduction of
`refs/latex/stellmacher-n-group.tex`, and GLS1, Chapter1, section28, formula (28.1).
-/

namespace Stellmacher

universe u

/-- Every prime-local subgroup of the finite group is solvable. -/
@[expose] public def IsNGroup (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup p Q →
    Group.IsSolvable (Subgroup.normalizer (Q : Set G))

/-- Thompson's all-prime condition implies the two-local condition. -/
public theorem isNTwoGroup_of_isNGroup
    {G : Type u} [Group G] [Finite G] (hN : IsNGroup G) : IsNTwoGroup G := by
  intro U hU
  obtain ⟨Q, hQ, hp, rfl⟩ := hU
  exact hN 2 Nat.prime_two Q hQ hp

end Stellmacher
