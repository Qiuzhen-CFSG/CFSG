module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Solvable

/-!
# Solvability of automorphism fixers of cyclic groups

The automorphism group of a cyclic group embeds in the abelian unit group
of ZMod. Its pointwise fixing subgroups are consequently solvable. This
includes the cyclic simple groups in the two-Schreier condition of
GLS II, Definition 2.2, without any odd-core-free hypothesis.
-/

namespace MulAut

/-- Every pointwise automorphism fixer of a cyclic group is solvable. -/
public theorem fixingSubgroup_solvable_of_isCyclic
    {G : Type*} [Group G] [IsCyclic G] (P : Subgroup G) :
    Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G)) := by
  let e := IsCyclic.mulAutMulEquiv G
  let : Group.IsSolvable (MulAut G) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  infer_instance

end MulAut
