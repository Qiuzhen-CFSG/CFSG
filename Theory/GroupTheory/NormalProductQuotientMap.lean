module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Quotient maps from a normal subgroup product

If K=VL with V normal in K, a surjection from L whose kernel is V∩L
extends to a quotient map on K with kernel V. The original inclusions and
quotient maps are retained throughout the second-isomorphism argument.
Source application: Aschbacher, Sporadic Groups (1994),45.7(3),p.245.
-/
public section
open Subgroup
namespace Subgroup
variable {G A:Type*} [Group G] [Group A]
theorem surjection_of_normal_product (K V L:Subgroup G)
    (hVK:V≤K) (hLK:L≤K) (hKV:K≤normalizer (V:Set G)) (hprod:K=V⊔L)
    (f:L→*A) (hf:Function.Surjective f) (hker:f.ker=V.subgroupOf L) :
    ∃ψ:K→*A,Function.Surjective ψ ∧ ψ.ker=V.subgroupOf K:=by
  let V':=V.subgroupOf K
  let : V'.Normal:=normal_subgroupOf_of_le_normalizer hKV
  let q:=QuotientGroup.mk' V'
  let i:L→*K:=inclusion hLK
  let g:=q.comp i
  have hsup:V'⊔L.subgroupOf K=⊤:=by
    apply map_injective K.subtype_injective
    rw[Subgroup.map_sup,map_subgroupOf_eq_of_le hVK,map_subgroupOf_eq_of_le hLK,
      ←MonoidHom.range_eq_map,range_subtype,←hprod]
  have hg:Function.Surjective g:=by
    apply MonoidHom.range_eq_top.mp
    have he:=congrArg (fun H:Subgroup K=>H.map q) hsup
    rw[Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,map_top_of_surjective q
      (QuotientGroup.mk'_surjective V')] at he
    have hir:i.range=L.subgroupOf K:=by
      ext k
      constructor
      · rintro ⟨l,rfl⟩;exact l.property
      · intro hk;exact ⟨⟨k,hk⟩,Subtype.ext rfl⟩
    rwa[MonoidHom.range_comp,hir]
  have hgker:g.ker=f.ker:=by
    rw[hker]
    ext l
    exact QuotientGroup.eq_one_iff (N:=V') (i l)
  let e: (K⧸V')≃*A:=(QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hgker).trans (QuotientGroup.quotientKerEquivOfSurjective f hf))
  refine ⟨e.toMonoidHom.comp q,e.surjective.comp (QuotientGroup.mk'_surjective V'),?_⟩
  ext k
  change e (q k)=1 ↔ k∈V'
  rw[←map_one e,e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff k
end Subgroup
