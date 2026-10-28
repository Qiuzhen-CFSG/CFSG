module

public import Theory.GroupTheory.SolvableRankOneStructure
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.SpecificGroups.GeneralizedQuaternionAut
public import Theory.GroupTheory.Fitting.PCoreAutomorphisms
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# The two-core of a solvable rank-one centralizer

A finite solvable group with trivial odd core and no elementary four is a
two-group unless its two-core is quaternion of order eight. The Fitting
subgroup equals the two-core and is self-centralizing. The absence of
an elementary four gives a unique involution in that core, so Huppert
III.8.2 makes it cyclic or generalized quaternion. In the cyclic case and
in quaternion orders greater than eight, its automorphism group is a
two-group, forcing the whole group to be a two-group.

This is the intrinsic group-theoretic structure step in the binary
centralizer rank-one reduction (GLS, Number 2, Proposition 22.4).
-/

namespace Stellmacher.Recognition

/-- A solvable group with trivial odd core and no elementary four is a
two-group, or its two-core is quaternion of order eight. -/
public theorem isPGroup_or_pCore_quaternion_of_rank_one
    {C : Type*} [Group C] [Finite C]
    (hsolv : Group.IsSolvable C) (hodd : pPrimeCore 2 C = ⊥)
    (hrank : ∀ F : Subgroup C, IsElementaryAbelian 2 F → Nat.card F < 4) :
    IsPGroup 2 C ∨ Nonempty (pCore 2 C ≃* QuaternionGroup 2) := by
  exact Group.isPGroup_or_pCore_quaternion_of_rank_one hsolv hodd hrank

end Stellmacher.Recognition
