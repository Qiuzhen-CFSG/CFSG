module
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The solvable residual of a normalized perfect subgroup and solvable supplement

If a solvable subgroup normalizes a perfect subgroup, the perfect subgroup
is the solvable residual of their join. The second isomorphism theorem
identifies the quotient with a solvable quotient of the supplement, while
perfectness supplies the reverse residual inclusion.

Source application: Aschbacher–Smith 10.2.10, printed p.753, where the
original point centralizer is the product of an A5 component and the
solvable point stabilizer of its conjugate.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- The literal embedded residual is the normalized perfect factor. -/
theorem map_solvableResidual_sup_eq_of_perfect_normalized
    (L N : Subgroup G) [Group.IsPerfect L] [Group.IsSolvable N]
    (hn : N ≤ normalizer (L : Set G)) :
    (solvableResidual (L ⊔ N : Subgroup G)).map (L ⊔ N).subtype = L := by
  suffices h : (solvableResidual (N ⊔ L : Subgroup G)).map (N ⊔ L).subtype = L by
    rw [sup_comm L N]
    exact h
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  let : (L.subgroupOf (N ⊔ L)).Normal := normal_subgroupOf_sup_of_le_normalizer hn
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient N L hn
  let : Group.IsSolvable ((N ⊔ L : Subgroup G) ⧸ L.subgroupOf (N ⊔ L)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  apply le_antisymm
  · have hm := map_mono (f := (N ⊔ L).subtype)
      (solvableResidual_le_of_solvable_quotient (L.subgroupOf (N ⊔ L)))
    rwa [map_subgroupOf_eq_of_le (show L ≤ N ⊔ L from le_sup_right)] at hm
  · exact le_map_solvableResidual_of_isPerfect L (N ⊔ L) le_sup_right
end Subgroup
