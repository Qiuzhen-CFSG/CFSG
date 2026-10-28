module

public import Theory.Character.ClassFunction
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The degree-21 character statement in Janko's argument

This interface states the character-theoretic input used both to construct the
index-22 subgroup and to identify its permutation character. The character is
afforded by an actual irreducible complex representation. The minimum degree,
uniqueness, and value table are separate mathematical assertions; this module
does not assert their existence from the involution-centralizer hypotheses.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, DOI 10.1016/0021-8693(68)90002-1, end of
Section 7, pp.15--16. The two order-four, order-seven, and order-eleven
classes have equal values and are combined here. The disjunction also asserts
that no other element orders occur, as required by the subsequent argument.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction

universe u

/-- The genuine irreducible character and the specific facts needed from
Janko's character calculation. Constructing this data is an upstream theorem. -/
public structure Degree21Character (G : Type u) [Group G] where
  chi : ClassFunction G
  irreducible : IsIrreducibleCharacter chi
  degree : chi 1 = 21
  minimum : ∀ theta : ClassFunction G, IsIrreducibleCharacter theta → theta ≠ 1 →
    (21 : ℝ) ≤ (theta 1).re
  unique : ∀ theta : ClassFunction G, IsIrreducibleCharacter theta →
    theta 1 = 21 → theta = chi
  values : ∀ g : G,
    (orderOf g = 1 ∧ chi g = 21) ∨
    (orderOf g = 2 ∧ chi g = 5) ∨
    (orderOf g = 3 ∧ chi g = 3) ∨
    (orderOf g = 4 ∧ chi g = 1) ∨
    (orderOf g = 5 ∧ chi g = 1) ∨
    (orderOf g = 6 ∧ chi g = -1) ∨
    (orderOf g = 7 ∧ chi g = 0) ∨
    (orderOf g = 8 ∧ chi g = -1) ∨
    (orderOf g = 11 ∧ chi g = -1)

/-- The order spectrum needed by the independent Sylow-normalizer argument. -/
public theorem Degree21Character.element_orders {G : Type u} [Group G]
    (C : Degree21Character G) (g : G) :
    orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ) := by
  rcases C.values g with ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ |
    ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩
  all_goals simp [ho]

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
