import Stellmacher.SectionsOneToFourDefs

open scoped BigOperators Pointwise

universe u

#check Subgroup.subgroupOf
#check Subgroup.IsSubnormal
#check Subgroup.IsSubnormal.trans
#check Subgroup.IsSubnormal.trans'
#check Subgroup.IsSubnormal.map
#check Subgroup.map
#check Subgroup.map_le_iff_le_comap
#check Subgroup.comap_subtype
#check Subgroup.subgroupOf_le
#check Subgroup.coe_subgroupOf
#check Subgroup.subtype
#check Subgroup.map_subtype
#check Subgroup.Normal
#check Subgroup.isSubnormal_iff
#check Subgroup.IsSubnormal.step

variable {G : Type u} [Group G]
variable (E L : Subgroup G)
variable (hEL : E ≤ L)

example : (E.subgroupOf L : Subgroup L).IsSubnormal → True := by
  intro h
  trivial

example (N : Subgroup G) (hNL : N ≤ L) :
    (N.subgroupOf L : Subgroup L).IsSubnormal → True := by
  intro h
  trivial

example (N : Subgroup G) (hNE : N ≤ E) (hEL : E ≤ L)
    (hsub : (N.subgroupOf E : Subgroup E).IsSubnormal) :
    (N.subgroupOf L : Subgroup L).IsSubnormal := by
  sorry

