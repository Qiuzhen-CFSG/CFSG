module
public import Theory.GroupTheory.CentralProductProjection.Marked
/-! # Projection on a literal intermediate subgroup
The commuting product is retained as its original subgroup, together with
the prescribed map on the first factor. Source application: AS 2.5.7.
-/
public section
open Subgroup
namespace Subgroup
variable {G Q:Type*} [Group G] [Group Q]
theorem exists_relative_marked_projection (A C R:Subgroup G)
    (hc:A≤centralizer (C:Set G)) (hgen:R=A⊔C)
    (q:A→*Q) (hq:q.ker=C.subgroupOf A) (hs:Function.Surjective q) :
    ∃f:R→*Q, f.comp (A.subgroupOf R).subtype=
        q.comp (subgroupOfEquivOfLe (show A≤R from hgen.symm ▸ le_sup_left)).toMonoidHom ∧
      f.ker=C.subgroupOf R ∧ Function.Surjective f := by
  have hAR:A≤R:=hgen.symm ▸ le_sup_left
  have hCR:C≤R:=hgen.symm ▸ le_sup_right
  let eA:=subgroupOfEquivOfLe hAR
  let q':(A.subgroupOf R)→*Q:=q.comp eA.toMonoidHom
  have hk:q'.ker=(C.subgroupOf R).subgroupOf (A.subgroupOf R):=by
    ext x
    change q (eA x)=1 ↔ ((x:R):G)∈C
    rw [←MonoidHom.mem_ker,hq]
    rfl
  have ht:A.subgroupOf R⊔C.subgroupOf R=⊤:=by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAR,map_subgroupOf_eq_of_le hCR,
      ←hgen,←MonoidHom.range_eq_map,R.range_subtype]
  have hc':A.subgroupOf R≤centralizer (C.subgroupOf R:Set R):=by
    intro a ha c hc'
    exact Subtype.ext (hc ha (c:G) hc')
  exact exists_marked_projection (A.subgroupOf R) (C.subgroupOf R) hc' ht q' hk
    (hs.comp eA.surjective)
end Subgroup
