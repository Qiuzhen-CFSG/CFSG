module
public import Theory.GroupTheory.CComponent.QuotientLifting
/-!
# Proper embeddings in a component survive normalized quotient kernels

Let B be a nontrivial perfect proper subgroup of a C-component K.
If a normal quotient kernel N normalizes B, equality of the two images
would put K inside BN and hence inside N_G(B). Then B is subnormal in
the ambient group, contradicting minimality of K.

This is the quotient step used for the proper local overcomponent in
Aschbacher--Smith 5.2.2, printed p.648. Its application to a two-core
retains the literal quotient map and proves kernel normalization from
the actual Sylow subgroup.
-/
public section
open Subgroup
namespace Subgroup.IsCComponent
variable {G : Type*} [Group G]

/-- A normal kernel normalizing the smaller perfect group cannot collapse
a proper embedding into a C-component. -/
theorem map_lt_of_kernel_normalizes {B K : Subgroup G}
    (hK : K.IsCComponent) (hBK : B < K) (hB : B ≠ ⊥) [Group.IsPerfect B]
    (N : Subgroup G) [N.Normal]
    (hNB : N ≤ normalizer (B : Set G)) :
    B.map (QuotientGroup.mk' N) < K.map (QuotientGroup.mk' N) := by
  refine lt_of_le_of_ne (map_mono hBK.le) ?_
  intro he
  have hKN : K ≤ B ⊔ N := by
    have hm := map_le_iff_le_comap.mp he.ge
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using hm
  have hKB : K ≤ normalizer (B : Set G) :=
    hKN.trans (sup_le B.le_normalizer hNB)
  have hn : (B.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBK.le).mpr hKB
  have hs : B.IsSubnormal := by
    have hh := hn.isSubnormal.trans' hK.subnormal
    simpa only [map_subgroupOf_eq_of_le hBK.le] using hh
  exact hBK.not_ge (hK.minimal B hBK.le hB inferInstance hs)

end Subgroup.IsCComponent
