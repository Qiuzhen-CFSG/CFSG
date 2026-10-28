module
public import Theory.GroupTheory.PResidual.SubnormalCorePreimage
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Two-perfect subgroups normalized by the core

If E is p-perfect and normalized by O_p(G), its product with O_p(G)
has p-group quotient over E. Thus E is exactly the p-residual of the
preimage of its image in G/O_p(G). When the latter quotient is abelian,
that preimage is normal, so E is normal as well.

This supplies the residual recovery in Aschbacher--Smith 15.2.23,
printed p.1116, without classifying arbitrary subgroups of an extension.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ}

/-- A p-perfect subgroup normalized by the p-core is normal if the core
quotient is abelian: recover it as the residual of its full image preimage. -/
theorem normal_of_isPPerfect_of_core_normalizes
    [IsMulCommutative (G ⧸ pCore p G)]
    (E : Subgroup G) (hp : IsPPerfect p E)
    (hn : pCore p G ≤ normalizer (E : Set G)) : E.Normal := by
  let N := pCore p G
  let U := E ⊔ N
  have hpre : U = (E.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
    rw [comap_map_eq,QuotientGroup.ker_mk']
  let : U.Normal := hpre ▸ inferInstance
  let A := E.subgroupOf U
  let B := N.subgroupOf U
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le E.le_normalizer hn)
  have hg : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup (show E ≤ U from le_sup_left) (show N ≤ U from le_sup_right),
      subgroupOf_self]
  let e := subgroupOfEquivOfLe (show E ≤ U from le_sup_left)
  have hA : IsPPerfect p A := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have he : (pResidual p U).map U.subtype = E := by
    rw [pResidual_eq_of_isPPerfect_sup A B hA pCore_isPGroup.comap_subtype hg,
      map_subgroupOf_eq_of_le le_sup_left]
  rw [← he]
  infer_instance

/-- The residual-preimage lift retains the original p-perfect subgroup. -/
theorem core_normalized_residual_preimage_eq
    [IsMulCommutative (G ⧸ pCore p G)]
    (E : Subgroup G) (hp : IsPPerfect p E)
    (hn : pCore p G ≤ normalizer (E : Set G)) :
    (pResidual p ((E.map (QuotientGroup.mk' (pCore p G))).comap
      (QuotientGroup.mk' (pCore p G)))).map
      ((E.map (QuotientGroup.mk' (pCore p G))).comap
        (QuotientGroup.mk' (pCore p G))).subtype = E :=
  residual_core_preimage_eq E
    (normal_of_isPPerfect_of_core_normalizes E hp hn).isSubnormal hp

end Theory.GroupTheory
