module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The derived group centralizes a cyclic normal subgroup

Conjugation on a cyclic normal subgroup takes values in an abelian
automorphism group. Thus it kills the derived group. This standard action
argument is used in Fong, J. Algebra 6 (1967), p.75, for an odd core of
order three.
-/

namespace Subgroup

public theorem commutator_le_centralizer_of_isCyclic_normal
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [IsCyclic N] :
    _root_.commutator G ≤ centralizer (N : Set G) := by
  let _ := (IsCyclic.mulAutMulEquiv N).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv N).injective
  have h := Abelianization.commutator_subset_ker N.normalizerMonoidHom
  rwa [normalizerMonoidHom_ker, normalizer_eq_top,
    ← map_subtype_le_map_subtype, map_subtype_commutator,
    map_subgroupOf_eq_of_le le_top] at h

end Subgroup
