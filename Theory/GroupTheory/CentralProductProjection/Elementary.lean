module
public import Theory.GroupTheory.CentralProductProjection.Relative
public import Theory.ElementaryAbelian.Injective
/-! # Original crossing preparation and marked quotients
The literal kernel and elementary plane preimages survive extension across a commuting factor.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
namespace Subgroup
variable {G Q:Type*} [Group G] [Group Q]
theorem exists_elementary_relative_projection (A C R:Subgroup G)
    (hc:A≤centralizer (C:Set G)) (hgen:R=A⊔C)
    (q:A→*Q) (hq:q.ker=C.subgroupOf A) (hs:Function.Surjective q)
    (hlift:∀W:Subgroup Q,IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q)) :
    ∃f:R→*Q, Function.Surjective (f.comp (A.subgroupOf R).subtype) ∧
      f.ker=C.subgroupOf R ∧ (A.subgroupOf R)≤centralizer (f.ker:Set R) ∧
      ∀W:Subgroup Q,IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp (A.subgroupOf R).subtype)) := by
  obtain ⟨f,hf,hk,hsf⟩:=exists_relative_marked_projection A C R hc hgen q hq hs
  let eA:=subgroupOfEquivOfLe (show A≤R from hgen.symm ▸ le_sup_left)
  refine ⟨f,?_,hk,?_,?_⟩
  · rw [hf]
    exact hs.comp eA.surjective
  · rw [hk]
    intro a ha c hc'
    exact Subtype.ext (hc ha (c:G) hc')
  · intro W hW
    rw [hf]
    let :=hlift W hW
    change IsElementaryAbelian 2 ((W.comap q).comap eA.toMonoidHom)
    exact IsElementaryAbelian.comap_of_injective eA.toMonoidHom eA.injective _
end Subgroup
