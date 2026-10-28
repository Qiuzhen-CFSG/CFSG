module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect normal subgroups of symmetric groups

A nontrivial normal subgroup of Sₙ, for n ≥ 5, contains Aₙ. If that
subgroup is perfect, its sign character is trivial, giving the reverse
containment. This identifies the actual component in a marked symmetric
natural action in Aschbacher–Smith, B.5.1(4b) and B.5.13, pp.99 and 111.
-/

public section
open Subgroup

namespace Equiv.Perm

/-- A nontrivial perfect normal subgroup of a symmetric group of degree at least five
is its alternating subgroup. -/
theorem eq_alternatingGroup_of_perfect_normal {α : Type*} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Nat.card α) (N : Subgroup (Perm α)) [N.Normal]
    [Group.IsPerfect N] [Nontrivial N] : N = alternatingGroup α := by
  apply le_antisymm
  · intro g hg
    apply mem_alternatingGroup.mpr
    exact Abelianization.commutator_subset_ker (sign.comp N.subtype)
      (Group.IsPerfect.mem_commutator (g := (⟨g, hg⟩ : N)))
  · exact alternatingGroup_le_of_normal hα inferInstance

end Equiv.Perm
