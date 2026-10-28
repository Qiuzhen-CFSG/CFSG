module

public import Theory.GroupTheory.SimpleSectionNormalAlternative
public import Mathlib.GroupTheory.Solvable

/-!
# Removing solvable layers from nonsolvable simple sections

A nonsolvable simple section of a group occurs in the quotient by any
solvable normal subgroup. If the quotient is solvable, the section occurs
in the normal subgroup instead. Apply the normal-image alternative and
exclude its solvable branch by closure of solvability under subgroups and
surjections. Neither finiteness nor an even-order hypothesis is needed.

We also record that a surjection from a simple group to a nontrivial group
is injective. This identifies the final quotient once a section numerator
has been identified as a simple group.

These are the elementary normal-layer reductions used in the maximal-
subgroup tables of the ATLAS, in particular the Mathieu entries on printed
pp. 18, 33, 40, 71 and 96.
-/

namespace Subgroup

/-- A solvable normal kernel cannot contain a nonsolvable simple section. -/
public theorem simple_section_quotient_of_solvable_kernel
    {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    ∃ W : Subgroup (G ⧸ N), ∃ g : W →* S, Function.Surjective g := by
  rcases simple_section_normal_or_quotient N U f hf with ⟨W, g, hg⟩ | h
  · exact False.elim (hS (Group.isSolvable_of_surjective hg))
  · exact h

/-- A solvable outer quotient contributes no nonsolvable simple section. -/
public theorem simple_section_normal_of_solvable_quotient
    {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)]
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    ∃ W : Subgroup N, ∃ g : W →* S, Function.Surjective g := by
  rcases simple_section_normal_or_quotient N U f hf with h | ⟨W, g, hg⟩
  · exact h
  · exact False.elim (hS (Group.isSolvable_of_surjective hg))

end Subgroup

/-- Every nontrivial quotient of a simple group is isomorphic to it. -/
public theorem MonoidHom.injective_of_surjective_of_simple
    {G S : Type*} [Group G] [IsSimpleGroup G] [Group S] [Nontrivial S]
    (f : G →* S) (hf : Function.Surjective f) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨g, rfl⟩ := hf s
    have hg : g ∈ f.ker := by rw [h]; trivial
    exact hs hg
